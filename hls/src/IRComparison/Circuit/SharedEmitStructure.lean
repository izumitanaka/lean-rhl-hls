import IRComparison.Circuit.SharedEmit
import IRComparison.Circuit.SystemVerilog.BooleanSound

namespace IRComparison.Circuit.Shared.NetEmission
open SystemVerilog

/-- Append-only declarations. This does not rely on an expression cache. -/
def Extends (before after : Wires) : Prop := ∃ extra, after = before ++ extra

theorem Extends.refl (s : Wires) : Extends s s := ⟨#[],by simp⟩
theorem Extends.trans (h : Extends a b) (k : Extends b c) : Extends a c := by
  obtain ⟨x,rfl⟩ := h
  obtain ⟨y,rfl⟩ := k
  exact ⟨x++y,by simp [Array.append_assoc]⟩
theorem Extends.size_le (h : Extends a b) : a.size ≤ b.size := by
  obtain ⟨x,rfl⟩ := h
  simp

def InScope (refs : Option (Array Signal)) (limit : Nat) : Prop :=
  ∀ xs, refs = some xs → ∀ signal ∈ xs.toList, signal.name.Before limit

theorem InScope.mono (h : InScope refs a) (hle : a ≤ b) : InScope refs b :=
  fun xs he signal hs => Name.before_mono (h xs he signal hs) hle

def Builds (refs : Option (Array Signal)) (action : Builder α) (post : α → Wires → Prop) : Prop :=
  ∀ before, SystemVerilog.Ordered 0 before.toList → InScope refs before.size → ∀ result after, action before = .ok (result,after) →
    SystemVerilog.Ordered 0 after.toList ∧ Extends before after ∧ post result after

theorem fresh_builds (scope : rhs.Before before.size)
    (good : SystemVerilog.Ordered 0 before.toList) (success : fresh rhs width before = .ok (signal,after)) :
    SystemVerilog.Ordered 0 after.toList ∧ Extends before after ∧ signal.name.Before after.size := by
  unfold fresh at success
  split at success
  · cases success
    refine ⟨?_,⟨#[⟨.temporary before.size,width,rhs,‹0 < width›⟩],by simp⟩,?_⟩
    · simp [Array.toList_push,ordered_append,SystemVerilog.Ordered,good,scope]
    · simp [Name.Before]
  · cases success

theorem mapM_builds (items : List α) (action : α → Builder Signal)
    (each : ∀ item ∈ items, Builds refs (action item) (fun signal st => signal.name.Before st.size)) :
    Builds refs (items.mapM action) (fun signals st => ∀ signal ∈ signals, signal.name.Before st.size) := by
  intro before good scope signals after success
  induction items generalizing before signals after with
  | nil =>
    obtain ⟨rfl,rfl⟩ := pure_success [] success
    exact ⟨good,.refl _,by simp⟩
  | cons item rest ih =>
    rw [List.mapM_cons] at success
    obtain ⟨head,middle,first,next⟩ := bind_success _ _ success
    obtain ⟨midGood,grows,headScope⟩ := each item (by simp) before good scope head middle first
    obtain ⟨tail,last,more,returned⟩ := bind_success _ _ next
    obtain ⟨afterGood,growsMore,tailScope⟩ := ih (fun x hx => each x (by simp [hx])) middle midGood (scope.mono grows.size_le) tail last more
    obtain ⟨rfl,rfl⟩ := pure_success (head::tail) returned
    refine ⟨afterGood,grows.trans growsMore,?_⟩
    intro signal member
    rcases List.mem_cons.mp member with rfl | member
    · exact Name.before_mono headScope growsMore.size_le
    · exact tailScope signal member

/-- The semantic use of local wire names is kept separate from external
holding registers. None means external; Some resolves only through refs. -/
def resolved (locals : Option (Array Signal)) (e : RTL.Term) : Option (Option Signal) :=
  match locals,e with
  | some refs,.wire n => some refs[n]?
  | _,_ => none

/-- Expose the actual emitter's local-reference/recursive cases uniformly. -/
theorem term_step (a : Artifact) (locals : Option (Array Signal)) (e : RTL.Term) :
    term a locals e =
      (match resolved locals e with
      | some (some signal) => pure signal
      | some none => throw (match e with | .wire n => s!"shared combinational reference {n} is not defined" | _ => "")
      | none => do
        let children ← e.children.attach.mapM fun child => term a locals child.val
        let (rhs,width) ← termTemplate a e children
        fresh rhs width) := by
  rw [term.eq_def]
  cases locals <;> cases e <;> simp [resolved]
  rename_i refs n
  cases h : refs[n]? <;> simp [h]
  rfl

theorem term_builds (a : Artifact) (locals : Option (Array Signal)) (e : RTL.Term)
    (before : Wires) (good : SystemVerilog.Ordered 0 before.toList) (scope : InScope locals before.size)
    (success : term a locals e before = .ok (signal,after)) :
    SystemVerilog.Ordered 0 after.toList ∧ Extends before after ∧ signal.name.Before after.size := by
  rw [term_step] at success
  cases found : resolved locals e with
  | some entry =>
    cases entry with
    | none =>
      simp only [found] at success
      change Except.error _ = Except.ok _ at success
      cases success
    | some ref =>
      simp only [found] at success
      obtain ⟨rfl,rfl⟩ := pure_success ref success
      refine ⟨good,.refl _,?_⟩
      cases locals <;> cases e <;> simp [resolved] at found
      rename_i refs n
      exact scope refs rfl _ (by simpa using Array.mem_of_getElem? found)
  | none =>
    simp only [found] at success
    obtain ⟨args,middle,children,next⟩ := bind_success _ _ success
    have each : ∀ child ∈ e.children.attach, Builds locals (term a locals child.val)
        (fun sig st => sig.name.Before st.size) := by
      intro child member start valid localScope sig finish compiled
      exact term_builds a locals child.val start valid localScope compiled
    obtain ⟨midGood,grows,argScope⟩ := mapM_builds _ _ each before good scope args middle children
    obtain ⟨pair,last,template,stored⟩ := bind_success _ _ next
    obtain ⟨compiled,rfl⟩ := lift_success _ template
    obtain ⟨afterGood,growsMore,signalScope⟩ := fresh_builds (termTemplate_scope a e args argScope compiled) midGood stored
    exact ⟨afterGood,grows.trans growsMore,signalScope⟩
termination_by sizeOf e
decreasing_by exact RTL.Term.child_size _ _ child.property

theorem validity_builds (a : Artifact) (locals : Option (Array Signal)) (v : RTL.Validity) :
    Builds locals (validity a locals v) (fun e st => e.Before st.size) := by
  intro before good scope expr after success
  induction v generalizing before expr after with
  | yes | no =>
    obtain ⟨rfl,rfl⟩ := pure_success _ success
    exact ⟨good,.refl _,trivial⟩
  | and u v ihu ihv =>
    rw [validity] at success
    obtain ⟨left,middle,first,next⟩ := bind_success _ _ success
    obtain ⟨right,second,rfl⟩ := map_success _ _ next
    obtain ⟨midGood,grows,leftScope⟩ := ihu before good scope left middle first
    obtain ⟨afterGood,more,rightScope⟩ := ihv middle midGood (scope.mono grows.size_le) right after second
    exact ⟨afterGood,grows.trans more,left.before_mono leftScope more.size_le,rightScope⟩
  | address n j =>
    rw [validity] at success
    obtain ⟨size,middle,found,next⟩ := bind_success _ _ success
    obtain ⟨known,stateEq⟩ := lift_success (memorySize a n) found
    subst middle
    obtain ⟨signal,compiled,rfl⟩ := return_success _ _ next
    obtain ⟨afterGood,grows,inScope⟩ := term_builds a locals j before good scope compiled
    exact ⟨afterGood,grows,⟨⟨inScope,trivial⟩,inScope,trivial⟩⟩
  | mux c u v ihu ihv =>
    rw [validity] at success
    obtain ⟨condition,middle,first,next⟩ := bind_success _ _ success
    obtain ⟨left,last,second,next⟩ := bind_success _ _ next
    obtain ⟨right,third,rfl⟩ := map_success _ _ next
    obtain ⟨midGood,grows,cScope⟩ := term_builds a locals c before good scope first
    obtain ⟨lastGood,more,lScope⟩ := ihu middle midGood (scope.mono grows.size_le) left last second
    obtain ⟨afterGood,latest,rScope⟩ := ihv last lastGood (scope.mono (grows.trans more).size_le) right after third
    refine ⟨afterGood,grows.trans (more.trans latest),?_⟩
    exact ⟨⟨Name.before_mono cScope (more.trans latest).size_le,trivial⟩,
      left.before_mono lScope latest.size_le,rScope⟩

def Pair.InScope (p : Pair) (limit : Nat) := p.value.name.Before limit ∧ p.valid.name.Before limit

theorem expression_builds (a : Artifact) (locals : Option (Array Signal)) (e : RTL.Combinational) :
    Builds locals (expression a locals e) (fun pair st => pair.InScope st.size) := by
  intro before good scope pair after success
  rw [expression] at success
  obtain ⟨value,middle,first,next⟩ := bind_success _ _ success
  obtain ⟨guard,last,second,next⟩ := bind_success _ _ next
  obtain ⟨valid,third,rfl⟩ := return_success _ _ next
  obtain ⟨midGood,grows,vScope⟩ := term_builds a locals e.value before good scope first
  obtain ⟨lastGood,more,gScope⟩ := validity_builds a locals e.valid middle midGood
    (scope.mono grows.size_le) guard last second
  obtain ⟨afterGood,latest,bScope⟩ := fresh_builds
    (rhs := .select guard (.integer 1) (.integer 0)) ⟨gScope,trivial,trivial⟩ lastGood third
  exact ⟨afterGood,grows.trans (more.trans latest),Name.before_mono vScope (more.trans latest).size_le,bScope⟩

theorem code_builds (a : Artifact) (refs : Array Signal) (c : LocalRTL.Code) :
    Builds (some refs) (code a refs c) (fun pair st => pair.InScope st.size) := by
  intro before good scope pair after success
  cases c with
  | source e => exact expression_builds a none e before good (by intro xs h; cases h) pair after success
  | localNode e => exact expression_builds a (some refs) e before good scope pair after success

theorem graph_builds (a : Artifact) (cs : List LocalRTL.Code) :
    Builds none (graph a cs) (fun refs st => InScope (some refs) st.size) := by
  intro before good scope refs after success
  induction cs generalizing before refs after with
  | nil =>
    obtain ⟨rfl,rfl⟩ := pure_success _ success
    exact ⟨good,.refl _,by simp [InScope]⟩
  | cons c cs ih =>
    rw [graph] at success
    obtain ⟨previous,middle,first,next⟩ := bind_success _ _ success
    obtain ⟨pair,second,rfl⟩ := return_success _ _ next
    obtain ⟨midGood,grows,prevScope⟩ := ih before good scope previous middle first
    obtain ⟨afterGood,more,pairScope⟩ := code_builds a previous c middle midGood prevScope pair after second
    refine ⟨afterGood,grows.trans more,?_⟩
    intro xs he signal member
    cases he
    simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
    rcases member with (member | rfl) | rfl
    · exact Name.before_mono (prevScope _ rfl signal member) more.size_le
    · exact pairScope.1
    · exact pairScope.2

theorem append_graph (success : append a p before = .ok (pair,after)) :
    ∃ refs, graph a p.code before = .ok (refs,after) ∧
      refs[2*p.result]? = some pair.value ∧ refs[2*p.result+1]? = some pair.valid := by
  unfold append at success
  cases built : graph a p.code before with
  | error why => simp [built,bind,Except.bind] at success
  | ok result =>
    obtain ⟨refs,decls⟩ := result
    simp only [built,bind,Except.bind] at success
    cases hv : refs[2*p.result]? with
    | none => simp [hv] at success
    | some value =>
      simp only [hv] at success
      cases hb : refs[2*p.result+1]? with
      | none => simp [hb] at success
      | some valid =>
        simp only [hb] at success
        cases success
        exact ⟨refs,rfl,hv,hb⟩

theorem generate_graph (success : generate a p = .ok output) :
    ∃ refs, graph a p.code #[] = .ok (refs,output.declarations) ∧
      refs[2*p.result]? = some output.result.value ∧ refs[2*p.result+1]? = some output.result.valid := by
  unfold generate at success
  cases built : append a p #[] with
  | error why => simp [built,Except.map] at success
  | ok result =>
    obtain ⟨pair,decls⟩ := result
    simp only [built,Except.map] at success
    cases success
    exact append_graph built

theorem generate_ordered (success : generate a p = .ok output) :
    SystemVerilog.Ordered 0 output.declarations.toList := by
  obtain ⟨refs,built,_,_⟩ := generate_graph success
  exact (graph_builds a p.code #[] trivial (by intro xs h; cases h) refs output.declarations built).1

end IRComparison.Circuit.Shared.NetEmission
