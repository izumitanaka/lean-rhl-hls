import IRComparison.Circuit.Width

/-! Shared combinational expressions. Node numbers name already computed
(value, validity) results, NOT clocked registers. This module is the verified
ReadCode lowering boundary; the existing main RTL route is not switched yet.
The old Expr is used as a proof specification and for the caller's input leaves.
No expansion into that tree is executed by the shared lowering function. -/
namespace IRComparison.Circuit.Shared

inductive Node where
  | input (e : Circuit.Expr)
  | memory (array index : Nat)
  | binary (op : Bin) (left right : Nat)
  | wrap32 (arg : Nat)
  | natIndex (arg : Nat)
  | select (condition yes no : Nat)
  | seq (first result : Nat)
  deriving Repr

abbrev Cache := Array (Option Int)
def get (cache : Cache) (ref : Nat) : Option Int := cache[ref]?.getD none

def Node.eval (s : State) (w : Nat → Int) (cache : Cache) : Node → Option Int
  | .input e => e.eval s w
  | .memory a j => do arrayInput (s.arrays a) (← get cache j)
  | .binary op a b => do return op.eval (← get cache a) (← get cache b)
  | .wrap32 a => do return (← get cache a) % 4294967296
  | .natIndex a => do return Int.ofNat (← get cache a).toNat
  | .select c a b => do if (← get cache c) != 0 then get cache a else get cache b
  | .seq a b => (get cache a).bind fun _ => get cache b

/-- Reverse topological order makes extending the graph constant-time. -/
abbrev Graph := List Node

/-- References always point strictly backward in the node sequence. -/
def Node.Scoped (size : Nat) : Node → Prop
  | .input _ => True
  | .memory _ j | .wrap32 j | .natIndex j => j < size
  | .binary _ a b | .seq a b => a < size ∧ b < size
  | .select c a b => c < size ∧ a < size ∧ b < size

def Ordered : Graph → Prop
  | [] => True
  | n::g => Ordered g ∧ n.Scoped g.length

variable {nextGraph : Graph}

def values (s : State) (w : Nat → Int) : Graph → Cache
  | [] => #[]
  | n::g => let cache := values s w g; cache.push (n.eval s w cache)

@[simp] theorem values_size (g : Graph) : (values s w g).size = g.length := by
  induction g with
  | nil => rfl
  | cons n g ih => simp [values,ih]

def Extends (before after : Graph) : Prop := ∃ added, after = added ++ before

theorem Extends.refl (g : Graph) : Extends g g := ⟨[],rfl⟩
theorem Extends.step (g : Graph) (n : Node) : Extends g (n::g) := ⟨[n],rfl⟩
theorem Extends.trans (h : Extends a b) (k : Extends b c) : Extends a c := by
  obtain ⟨p,rfl⟩ := h
  obtain ⟨q,rfl⟩ := k
  exact ⟨q++p,by simp [List.append_assoc]⟩

theorem Extends.length (h : Extends a b) : a.length ≤ b.length := by
  obtain ⟨p,rfl⟩ := h
  simp

theorem Extends.get (h : Extends a b) (inside : ref < a.length) :
    get (values s w b) ref = get (values s w a) ref := by
  obtain ⟨p,rfl⟩ := h
  induction p with
  | nil => rfl
  | cons n p ih =>
    have bound : ref < (values s w (p ++ a)).size := by simp; omega
    change ((values s w (p ++ a)).push _)[ref]?.getD none = _
    rw [Array.getElem?_push_lt bound]
    unfold Shared.get at ih
    rw [Array.getElem?_eq_getElem bound] at ih
    exact ih

/- Executable builder data contains only references and the actual graph.
Source expression specifications are absent from recursive-call arguments. -/
namespace Raw
structure Context where
  index : Nat
  left : Nat
  right : Nat
  locals : List Nat
  temps : List Nat

structure Result where
  graph : Graph
  ref : Nat

def append (g : Graph) (n : Node) : Result := ⟨n::g,g.length⟩
def lookup (g : Graph) (refs : List Nat) (n : Nat) : Result :=
  match refs[n]? with
  | none => append g (.input .fail)
  | some ref => ⟨g,ref⟩

def value (g : Graph) (c : Context) : HybridIR.Value → Result
  | .lit n => append g (.input (.lit n))
  | .index => ⟨g,c.index⟩
  | .left => ⟨g,c.left⟩
  | .right => ⟨g,c.right⟩
  | .local n => lookup g c.locals n
  | .temp n => lookup g c.temps n
  | .wrap32 v => let a := value g c v; append a.graph (.wrap32 a.ref)
  | .natIndex v => let a := value g c v; append a.graph (.natIndex a.ref)
  | .add u v => let a := value g c u; let b := value a.graph c v; append b.graph (.binary .add a.ref b.ref)
  | .sub u v => let a := value g c u; let b := value a.graph c v; append b.graph (.binary .sub a.ref b.ref)
  | .mul u v => let a := value g c u; let b := value a.graph c v; append b.graph (.binary .mul a.ref b.ref)
  | .div u v => let a := value g c u; let b := value a.graph c v; append b.graph (.binary .div a.ref b.ref)

def read (g : Graph) (c : Context) : HybridIR.ReadCode → Result
  | .pure v => value g c v
  | .register r => append g (.input (.reg r))
  | .memory a j => let index := value g c j; append index.graph (.memory a index.ref)
  | .bind first next =>
    let a := read g c first
    let b := read a.graph {c with temps := a.ref::c.temps} next
    append b.graph (.seq a.ref b.ref)
  | .branch test yes no =>
    let t := value g c test
    let a := read t.graph c yes
    let b := read a.graph c no
    append b.graph (.select t.ref a.ref b.ref)

structure Inputs where
  graph : Graph
  refs : List Nat

def inputs (g : Graph) : List Circuit.Expr → Inputs
  | [] => ⟨g,[]⟩
  | e::es =>
    let a := append g (.input e)
    let rest := inputs a.graph es
    ⟨rest.graph,a.ref::rest.refs⟩

def build (i x y : Circuit.Expr) (ls ts : List Circuit.Expr) (r : HybridIR.ReadCode) : Result :=
  let a := append [] (.input i)
  let b := append a.graph (.input x)
  let c := append b.graph (.input y)
  let l := inputs c.graph ls
  let t := inputs l.graph ts
  read t.graph ⟨a.ref,b.ref,c.ref,l.refs,t.refs⟩ r
end Raw

/- The following proof construction is deliberately noncomputable. It relates
Raw's executable, reference-only recursion to the old expression denotation.
Only its projection-equality theorems are used by the public compiler. -/
noncomputable section Certification

/-- A reference carries a generic denotation proof. Expr occurs only in the
proof index; compiler execution does not construct its expanded tree. -/
structure Link (g : Graph) (e : Circuit.Expr) where
  ref : Nat
  inside : ref < g.length
  correct : ∀ s w, get (values s w g) ref = e.eval s w

noncomputable def Link.lift (l : Link g e) (h : Extends g nextGraph) : Link nextGraph e :=
  ⟨l.ref,Nat.lt_of_lt_of_le l.inside h.length,fun s w => (h.get l.inside).trans (l.correct s w)⟩

structure Built (g : Graph) (e : Circuit.Expr) where
  graph : Graph
  extension : Extends g graph
  ordered : Ordered g → Ordered graph
  link : Link graph e

noncomputable def reuse (l : Link g e) : Built g e := ⟨g,.refl g,fun h => h,l⟩

noncomputable def append (g : Graph) (node : Node) (e : Circuit.Expr) (inScope : node.Scoped g.length)
    (sound : ∀ s w, node.eval s w (values s w g) = e.eval s w) : Built g e :=
  ⟨node::g,.step g node,fun h => ⟨h,inScope⟩,⟨g.length,by simp,by
    intro s w
    change ((values s w g).push _)[g.length]?.getD none = _
    rw [← values_size (s:=s) (w:=w) g,Array.getElem?_push_size]
    exact sound s w⟩⟩

noncomputable def input (g : Graph) (e : Circuit.Expr) : Built g e := append g (.input e) e trivial (by intros; rfl)

noncomputable def binary (a : Link g ea) (b : Link g eb) (op : Bin) : Built g (.bin op ea eb) :=
  append g (.binary op a.ref b.ref) _ ⟨a.inside,b.inside⟩ (by
    intro s w
    simp [Node.eval,Circuit.Expr.eval,a.correct,b.correct])

noncomputable def wrap32 (a : Link g e) : Built g (.wrap32 e) :=
  append g (.wrap32 a.ref) _ a.inside (by intro s w; simp [Node.eval,Circuit.Expr.eval,a.correct])
noncomputable def natIndex (a : Link g e) : Built g (.natIndex e) :=
  append g (.natIndex a.ref) _ a.inside (by intro s w; simp [Node.eval,Circuit.Expr.eval,a.correct])
noncomputable def memory (a : Nat) (j : Link g e) : Built g (.memory a e) :=
  append g (.memory a j.ref) _ j.inside (by intro s w; simp [Node.eval,Circuit.Expr.eval,j.correct])
noncomputable def seq (a : Link g ea) (b : Link g eb) : Built g (.seq ea eb) :=
  append g (.seq a.ref b.ref) _ ⟨a.inside,b.inside⟩ (by intro s w; simp [Node.eval,Circuit.Expr.eval,a.correct,b.correct])
noncomputable def select (c : Link g ec) (a : Link g ea) (b : Link g eb) : Built g (.select ec ea eb) :=
  append g (.select c.ref a.ref b.ref) _ ⟨c.inside,a.inside,b.inside⟩ (by
    intro s w
    simp [Node.eval,Circuit.Expr.eval,c.correct,a.correct,b.correct])

/-- Compose already-built graph fragments without recomputing any node. -/
noncomputable def Built.then (a : Built g ea) (b : Built a.graph eb) : Built g eb :=
  ⟨b.graph,a.extension.trans b.extension,fun h => b.ordered (a.ordered h),b.link⟩

/-- Runtime environment: node numbers only. The relationship to old Exprs is
an erased proposition, not an indexed inductive carrying existential indices. -/
inductive RefMatches (g : Graph) : List Nat → List Circuit.Expr → Prop where
  | nil : RefMatches g [] []
  | cons (head : ref < g.length ∧ ∀ s w, get (values s w g) ref = e.eval s w)
      (tail : RefMatches g refs es) : RefMatches g (ref::refs) (e::es)

structure Links (g : Graph) (es : List Circuit.Expr) where
  refs : List Nat
  valid : RefMatches g refs es

noncomputable def Links.nil : Links g [] := ⟨[],.nil⟩

noncomputable def Links.cons (head : Link g e) (tail : Links g es) : Links g (e::es) :=
  ⟨head.ref::tail.refs,.cons ⟨head.inside,head.correct⟩ tail.valid⟩

noncomputable def Links.lift (ls : Links g es) (h : Extends g nextGraph) : Links nextGraph es :=
  ⟨ls.refs,by
    obtain ⟨refs,valid⟩ := ls
    induction valid with
    | nil => exact .nil
    | cons head tail ih =>
      exact .cons ⟨Nat.lt_of_lt_of_le head.1 h.length,
        fun s w => (h.get head.1).trans (head.2 s w)⟩ ih⟩

theorem Links.lookup_spec (ls : Links g es) (n : Nat) :
    match ls.refs[n]? with
    | none => Circuit.lookup es n = .fail
    | some ref => ref < g.length ∧
      ∀ s w, get (values s w g) ref = (Circuit.lookup es n).eval s w := by
  obtain ⟨refs,valid⟩ := ls
  induction valid generalizing n with
  | nil => simp [Circuit.lookup]
  | cons head tail ih =>
    cases n with
    | zero => simpa [Circuit.lookup] using head
    | succ n => simpa [Circuit.lookup] using ih n

noncomputable def Links.lookup (ls : Links g es) (n : Nat) : Built g (Circuit.lookup es n) :=
  match h : ls.refs[n]? with
  | none => append g (.input .fail) _ trivial (by
      have hh := ls.lookup_spec n
      rw [h] at hh
      intro s w
      simp [Node.eval,hh])
  | some ref => reuse ⟨ref,by have hh := ls.lookup_spec n; rw [h] at hh; exact hh.1,
      by have hh := ls.lookup_spec n; rw [h] at hh; exact hh.2⟩

structure Context (g : Graph) (i x y : Circuit.Expr) (locals temps : List Circuit.Expr) where
  index : Link g i
  left : Link g x
  right : Link g y
  localValues : Links g locals
  temporaryValues : Links g temps

noncomputable def Context.lift (c : Context g i x y ls ts) (h : Extends g nextGraph) : Context nextGraph i x y ls ts :=
  ⟨c.index.lift h,c.left.lift h,c.right.lift h,c.localValues.lift h,c.temporaryValues.lift h⟩

noncomputable def Context.bind (c : Context g i x y ls ts) (a : Link g e) : Context g i x y ls (e::ts) :=
  {c with temporaryValues := .cons a c.temporaryValues}

noncomputable def lowerValue (c : Context g i x y ls ts) :
    (v : HybridIR.Value) → Built g (Circuit.value i x y ls ts v)
  | .lit n => input g (.lit n)
  | .index => reuse c.index
  | .left => reuse c.left
  | .right => reuse c.right
  | .local n => c.localValues.lookup n
  | .temp n => c.temporaryValues.lookup n
  | .wrap32 v =>
      let a := lowerValue c v
      a.then (wrap32 a.link)
  | .natIndex v =>
      let a := lowerValue c v
      a.then (natIndex a.link)
  | .add u v =>
      let a := lowerValue c u
      let b := lowerValue (c.lift a.extension) v
      a.then (b.then (binary (a.link.lift b.extension) b.link .add))
  | .sub u v =>
      let a := lowerValue c u
      let b := lowerValue (c.lift a.extension) v
      a.then (b.then (binary (a.link.lift b.extension) b.link .sub))
  | .mul u v =>
      let a := lowerValue c u
      let b := lowerValue (c.lift a.extension) v
      a.then (b.then (binary (a.link.lift b.extension) b.link .mul))
  | .div u v =>
      let a := lowerValue c u
      let b := lowerValue (c.lift a.extension) v
      a.then (b.then (binary (a.link.lift b.extension) b.link .div))

/-- Total structural lowering. The bind's value and validity are reused by
reference; its seq guard remains even if the continuation ignores the value.
Both branches may have cached partial results, but select observes only one. -/
noncomputable def lowerRead (c : Context g i x y ls ts) :
    (r : HybridIR.ReadCode) → Built g (Circuit.read i x y ls ts r)
  | .pure v => lowerValue c v
  | .register r => input g (.reg r)
  | .memory a j =>
      let index := lowerValue c j
      index.then (memory a index.link)
  | .bind first next =>
      let a := lowerRead c first
      let b := lowerRead ((c.lift a.extension).bind a.link) next
      a.then (b.then (seq (a.link.lift b.extension) b.link))
  | .branch test yes no =>
      let t := lowerValue c test
      let a := lowerRead (c.lift t.extension) yes
      let b := lowerRead (c.lift (t.extension.trans a.extension)) no
      t.then (a.then (b.then (select (t.link.lift (a.extension.trans b.extension))
        (a.link.lift b.extension) b.link)))

/-- Generic denotation theorem, including failures; no source-input execution
or successful-read premise is used to certify individual programs. -/
theorem lowerRead_correct (c : Context g i x y ls ts) (r : HybridIR.ReadCode) (s : State) (w : Nat → Int) :
    let built := lowerRead c r
    get (values s w built.graph) built.link.ref = (Circuit.read i x y ls ts r).eval s w :=
  (lowerRead c r).link.correct s w

structure BuiltLinks (g : Graph) (es : List Circuit.Expr) where
  graph : Graph
  extension : Extends g graph
  ordered : Ordered g → Ordered graph
  links : Links graph es

noncomputable def inputs (g : Graph) : (es : List Circuit.Expr) → BuiltLinks g es
  | [] => ⟨g,.refl g,fun h => h,.nil⟩
  | e::es =>
      let a := input g e
      let rest := inputs a.graph es
      ⟨rest.graph,a.extension.trans rest.extension,fun h => rest.ordered (a.ordered h),
        .cons (a.link.lift rest.extension) rest.links⟩

noncomputable def build (i x y : Circuit.Expr) (ls ts : List Circuit.Expr) (r : HybridIR.ReadCode) :
    Built [] (Circuit.read i x y ls ts r) :=
  let a := input [] i
  let b := input a.graph x
  let c := input b.graph y
  let l := inputs c.graph ls
  let t := inputs l.graph ts
  let ctx : Context t.graph i x y ls ts :=
    ⟨a.link.lift (b.extension.trans (c.extension.trans (l.extension.trans t.extension))),
     b.link.lift (c.extension.trans (l.extension.trans t.extension)),
     c.link.lift (l.extension.trans t.extension),l.links.lift t.extension,t.links⟩
  let result := lowerRead ctx r
  ⟨result.graph,a.extension.trans (b.extension.trans (c.extension.trans
    (l.extension.trans (t.extension.trans result.extension)))),
    fun h => result.ordered (t.ordered (l.ordered (c.ordered (b.ordered (a.ordered h))))),result.link⟩

noncomputable def Context.erase (c : Context g i x y ls ts) : Raw.Context :=
  ⟨c.index.ref,c.left.ref,c.right.ref,c.localValues.refs,c.temporaryValues.refs⟩

@[simp] theorem Context.erase_lift (c : Context g i x y ls ts) (h : Extends g nextGraph) :
    (c.lift h).erase = c.erase := rfl

@[simp] theorem Context.erase_bind (c : Context g i x y ls ts) (a : Link g e) :
    (c.bind a).erase = {c.erase with temps := a.ref::c.erase.temps} := rfl

theorem Links.lookup_projection (ls : Links g es) (n : Nat) :
    (ls.lookup n).graph = (Raw.lookup g ls.refs n).graph ∧
    (ls.lookup n).link.ref = (Raw.lookup g ls.refs n).ref := by
  unfold Links.lookup Raw.lookup
  split <;> simp_all [append,Raw.append,reuse]

theorem lowerValue_projection (c : Context g i x y ls ts) (v : HybridIR.Value) :
    (lowerValue c v).graph = (Raw.value g c.erase v).graph ∧
    (lowerValue c v).link.ref = (Raw.value g c.erase v).ref := by
  induction v generalizing g i x y ls ts with
  | lit | index | left | right =>
    simp [lowerValue,Raw.value,Raw.append,input,append,reuse,Context.erase]
  | «local» n => exact c.localValues.lookup_projection n
  | temp n => exact c.temporaryValues.lookup_projection n
  | wrap32 v ih | natIndex v ih =>
    obtain ⟨hg,hr⟩ := ih c
    simp [lowerValue,Raw.value,Built.then,wrap32,natIndex,append,Raw.append,hg,hr]
  | add u v ihu ihv | sub u v ihu ihv | mul u v ihu ihv | div u v ihu ihv =>
    obtain ⟨hg,hr⟩ := ihu c
    obtain ⟨jg,jr⟩ := ihv (c.lift (lowerValue c u).extension)
    simp only [Context.erase_lift] at jg jr
    simp [lowerValue,Raw.value,Built.then,binary,append,Raw.append,Link.lift,jg,jr,hg,hr]

theorem lowerRead_projection (c : Context g i x y ls ts) (r : HybridIR.ReadCode) :
    (lowerRead c r).graph = (Raw.read g c.erase r).graph ∧
    (lowerRead c r).link.ref = (Raw.read g c.erase r).ref := by
  induction r generalizing g i x y ls ts with
  | pure v => exact lowerValue_projection c v
  | register r => simp [lowerRead,Raw.read,input,append,Raw.append]
  | memory a j =>
    obtain ⟨hg,hr⟩ := lowerValue_projection c j
    simp [lowerRead,Raw.read,memory,append,Raw.append,Built.then,hg,hr]
  | bind first next ihf ihn =>
    obtain ⟨hg,hr⟩ := ihf c
    obtain ⟨jg,jr⟩ := ihn ((c.lift (lowerRead c first).extension).bind (lowerRead c first).link)
    simp only [Context.erase_bind,Context.erase_lift] at jg jr
    simp [lowerRead,Raw.read,seq,append,Raw.append,Built.then,Link.lift,jg,jr,hg,hr]
  | branch test yes no ihy ihn =>
    obtain ⟨tg,tr⟩ := lowerValue_projection c test
    obtain ⟨ag,ar⟩ := ihy (c.lift (lowerValue c test).extension)
    obtain ⟨bg,br⟩ := ihn (c.lift ((lowerValue c test).extension.trans
      (lowerRead (c.lift (lowerValue c test).extension) yes).extension))
    simp only [Context.erase_lift] at ag ar bg br
    simp [lowerRead,Raw.read,select,append,Raw.append,Built.then,Link.lift,bg,br,ag,ar,tg,tr]

theorem inputs_projection (g : Graph) (es : List Circuit.Expr) :
    (inputs g es).graph = (Raw.inputs g es).graph ∧
    (inputs g es).links.refs = (Raw.inputs g es).refs := by
  induction es generalizing g with
  | nil => simp [inputs,Raw.inputs,Links.nil]
  | cons e es ih =>
    obtain ⟨hg,hr⟩ := ih ((input g e).graph)
    simp [inputs,Raw.inputs,Links.cons,Links.lift,Link.lift,hg,hr,input,append,Raw.append] at *

theorem build_projection (i x y : Circuit.Expr) (ls ts : List Circuit.Expr) (r : HybridIR.ReadCode) :
    (build i x y ls ts r).graph = (Raw.build i x y ls ts r).graph ∧
    (build i x y ls ts r).link.ref = (Raw.build i x y ls ts r).ref := by
  simp only [build,Raw.build]
  simp only [(lowerRead_projection _ r).1,(lowerRead_projection _ r).2]
  simp [Context.erase,Link.lift,Links.lift,input,append,Raw.append,
    (inputs_projection _ ls).1,(inputs_projection _ ls).2,
    (inputs_projection _ ts).1,(inputs_projection _ ts).2]

end Certification

structure Program where
  graph : Graph
  result : Nat
  deriving Repr

def Program.eval (p : Program) (s : State) (w : Nat → Int) : Option Int :=
  get (values s w p.graph) p.result

/-- No search budget or acceptance test: every ReadCode has a shared graph.
This is an IR-to-IR total function, not the unfinished ordinary-Lean frontend
completeness theorem. -/
def compile (i x y : Circuit.Expr) (ls ts : List Circuit.Expr) (r : HybridIR.ReadCode) : Program :=
  let p := Raw.build i x y ls ts r
  ⟨p.graph,p.ref⟩

theorem compile_ordered (i x y : Circuit.Expr) (ls ts : List Circuit.Expr) (r : HybridIR.ReadCode) :
    Ordered (compile i x y ls ts r).graph := by
  simpa only [compile,← (build_projection i x y ls ts r).1] using (build i x y ls ts r).ordered trivial

theorem compile_result_bound (i x y : Circuit.Expr) (ls ts : List Circuit.Expr) (r : HybridIR.ReadCode) :
    (compile i x y ls ts r).result < (compile i x y ls ts r).graph.length :=
  by simpa only [compile,← (build_projection i x y ls ts r).1,← (build_projection i x y ls ts r).2] using (build i x y ls ts r).link.inside

theorem compile_correct (i x y : Circuit.Expr) (ls ts : List Circuit.Expr)
    (r : HybridIR.ReadCode) (s : State) (w : Nat → Int) :
    (compile i x y ls ts r).eval s w = (Circuit.read i x y ls ts r).eval s w :=
  by simpa only [compile,Program.eval,← (build_projection i x y ls ts r).1,← (build_projection i x y ls ts r).2] using (build i x y ls ts r).link.correct s w

theorem compile_read_correct (r : HybridIR.ReadCode)
    (hi : i.eval s w = some iv) (hx : x.eval s w = some xv) (hy : y.eval s w = some yv)
    (hl : Matches s w ls lvs) (ht : Matches s w ts tvs) :
    (compile i x y ls ts r).eval s w = r.eval iv xv yv s lvs tvs :=
  (compile_correct i x y ls ts r s w).trans (read_correct r hi hx hy hl ht)

end IRComparison.Circuit.Shared
