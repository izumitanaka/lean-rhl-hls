import IRComparison.Circuit.SharedBit
import IRComparison.Circuit.RTL.Combinational

namespace IRComparison.Circuit.Shared
namespace LocalRTL

/-- Local combinational names: even slot = value, odd slot = validity.
These are NOT clocked holding registers; emission must resolve them to nets. -/
def valueRef (n : Nat) : RTL.Term := .wire (2*n)
def validRef (n : Nat) : RTL.Validity := .mux (.wire (2*n+1)) .yes .no

def wires (cache : Cache) (k : Nat) : Int :=
  if k % 2 = 0 then (get cache (k/2)).getD 0
  else if (get cache (k/2)).isSome then 1 else 0

def runtime (r : Runtime) (cache : Cache) : Runtime := {r with wires := wires cache}

@[simp] theorem runtime_data (r : Runtime) (cache : Cache) : (runtime r cache).data = r.data := rfl

@[simp] theorem valueRef_eval (r : Runtime) (cache : Cache) (n : Nat) :
    (valueRef n).eval (runtime r cache) = (get cache n).getD 0 := by
  simp [valueRef,RTL.Term.eval,runtime,wires]

@[simp] theorem validRef_eval (r : Runtime) (cache : Cache) (n : Nat) :
    (validRef n).eval (runtime r cache) = (get cache n).isSome := by
  have h : (2*n+1)/2 = n := by omega
  simp [validRef,RTL.Validity.eval,RTL.Term.eval,runtime,wires,h]
  cases get cache n <;> rfl

/-- Caller inputs use the external environment. Other nodes use local
combinational references. The distinction prevents identifier collisions. -/
inductive Code where
  | source (code : RTL.Combinational)
  | localNode (code : RTL.Combinational)
  deriving Repr

def Code.eval (r : Runtime) (cache : Cache) : Code → Option Int
  | .source code => code.eval r
  | .localNode code => code.eval (runtime r cache)

def raw (n : Shared.Node) : RTL.Term × RTL.Validity :=
  match n with
  | .input _ => ⟨.literal 0,.no⟩ -- handled by lower's source case
  | .memory a j => ⟨.cell a (valueRef j),.and (validRef j) (.address a (valueRef j))⟩
  | .binary op a b => ⟨.binary op (valueRef a) (valueRef b),.and (validRef a) (validRef b)⟩
  | .wrap32 a => ⟨.wrap32 (valueRef a),validRef a⟩
  | .natIndex a => ⟨.nonnegative (valueRef a),validRef a⟩
  | .select c a b => ⟨.mux (valueRef c) (valueRef a) (valueRef b),
      .and (validRef c) (.mux (valueRef c) (validRef a) (validRef b))⟩
  | .seq a b => ⟨valueRef b,.and (validRef a) (validRef b)⟩

def lower (wr : Nat → Interval) (rs : Array Interval) (n : Shared.Node) : Code :=
  match n with
  | .input e => .source (RTL.combinational wr e)
  | _ =>
    let (v,ok) := raw n
    .localNode ⟨.resize (signedWidth (n.range wr rs)) v,ok,n.range wr rs⟩

theorem raw_correct {outputBounds : Interval} (n : Shared.Node) (notInput : ∀ e, n ≠ .input e) :
    (RTL.Combinational.mk (raw n).1 (raw n).2 outputBounds).eval (runtime r cache) =
      n.bitRaw wr r.data r.wires cache := by
  cases n with
  | input e => exact False.elim (notInput e rfl)
  | memory a j =>
    cases hj : get cache j with
    | none => simp [raw,RTL.Combinational.eval,RTL.Validity.eval,hj,Shared.Node.bitRaw,Shared.Node.eval]
    | some index =>
      by_cases hn : index < 0
      · simp [raw,RTL.Combinational.eval,RTL.Validity.eval,RTL.Term.eval,valueRef_eval,
          hj,Shared.Node.bitRaw,Shared.Node.eval,arrayInput,hn,show ¬0 ≤ index from by omega]
      · by_cases hi : index.toNat < (r.data.arrays a).size
        · simp [raw,RTL.Combinational.eval,RTL.Validity.eval,RTL.Term.eval,valueRef_eval,
            hj,Shared.Node.bitRaw,Shared.Node.eval,arrayInput,hn,hi,show 0 ≤ index from by omega]
        · simp [raw,RTL.Combinational.eval,RTL.Validity.eval,RTL.Term.eval,valueRef_eval,
            hj,Shared.Node.bitRaw,Shared.Node.eval,arrayInput,hn,hi,show 0 ≤ index from by omega]
  | binary op a b =>
    cases ha : get cache a <;> cases hb : get cache b <;>
      simp [raw,RTL.Combinational.eval,RTL.Validity.eval,RTL.Term.eval,ha,hb,Shared.Node.bitRaw]
  | wrap32 a | natIndex a =>
    cases ha : get cache a <;>
      simp [raw,RTL.Combinational.eval,RTL.Term.eval,ha,Shared.Node.bitRaw,Shared.Node.eval]
  | seq a b =>
    cases ha : get cache a <;> cases hb : get cache b <;>
      simp [raw,RTL.Combinational.eval,RTL.Validity.eval,ha,hb,Shared.Node.bitRaw,Shared.Node.eval]
  | select c a b =>
    cases hc : get cache c <;> cases ha : get cache a <;> cases hb : get cache b <;>
      simp [raw,RTL.Combinational.eval,RTL.Validity.eval,RTL.Term.eval,hc,ha,hb,
        Shared.Node.bitRaw,Shared.Node.eval] <;> split <;> simp_all

theorem lower_correct (n : Shared.Node) :
    (lower wr rs n).eval r cache = n.bitEval wr rs r.data r.wires cache := by
  by_cases h : ∃ e, n = .input e
  · obtain ⟨e,rfl⟩ := h
    simp only [lower,Code.eval,RTL.combinational_correct,Shared.Node.bitEval,Shared.Node.bitRaw,Shared.Node.range]
    unfold Circuit.Expr.bitEval
    simp only [Option.map_map,Function.comp_def,BitVec.ofInt_toInt]
  · have hn : ∀ e, n ≠ .input e := by simpa using h
    have shape : lower wr rs n = .localNode
        ⟨.resize (signedWidth (n.range wr rs)) (raw n).1,(raw n).2,n.range wr rs⟩ := by
      cases n <;> simp_all [lower]
    rw [shape,Code.eval,RTL.Combinational.resize_eval
      (⟨(raw n).1,(raw n).2,n.range wr rs⟩ : RTL.Combinational),raw_correct n hn]
    rfl

structure Lowered where
  ranges : Array Interval
  code : List Code

def lowerGraph (wr : Nat → Interval) : Graph → Lowered
  | [] => ⟨#[],[]⟩
  | n::g =>
    let rest := lowerGraph wr g
    ⟨rest.ranges.push (n.range wr rest.ranges),lower wr rest.ranges n::rest.code⟩

def evalGraph (r : Runtime) : List Code → Cache
  | [] => #[]
  | n::ns => let cache := evalGraph r ns; cache.push (n.eval r cache)

theorem lowerGraph_correct (g : Graph) :
    (lowerGraph wr g).ranges = (bitValues wr r.data r.wires g).ranges ∧
    evalGraph r (lowerGraph wr g).code = (bitValues wr r.data r.wires g).cache := by
  induction g with
  | nil => exact ⟨rfl,rfl⟩
  | cons n g ih => simp [lowerGraph,bitValues,evalGraph,ih.1,ih.2,lower_correct]

theorem lowerGraph_size (g : Graph) : (lowerGraph wr g).code.length = g.length := by
  induction g with
  | nil => rfl
  | cons n g ih => simp [lowerGraph,ih]

structure Program where
  code : List Code
  result : Nat

def compile (wr : Nat → Interval) (p : Shared.Program) : Program :=
  ⟨(lowerGraph wr p.graph).code,p.result⟩

def Program.eval (p : Program) (r : Runtime) : Option Int := get (evalGraph r p.code) p.result

theorem compile_bit_correct (p : Shared.Program) (r : Runtime) :
    (compile wr p).eval r = p.bitEval wr r.data r.wires := by
  simp only [compile,Program.eval,Shared.Program.bitEval,(lowerGraph_correct p.graph).2]

theorem compile_correct (p : Shared.Program) (hb : InputsBound r.data r.wires wr) :
    (compile wr p).eval r = p.eval r.data r.wires :=
  (compile_bit_correct p r).trans (p.bitEval_correct hb)

theorem compile_read_correct (r : HybridIR.ReadCode) (hb : InputsBound state.data state.wires wr)
    (hi : i.eval state.data state.wires = some iv)
    (hx : x.eval state.data state.wires = some xv)
    (hy : y.eval state.data state.wires = some yv)
    (hl : Matches state.data state.wires ls lvs) (ht : Matches state.data state.wires ts tvs) :
    (compile wr (Shared.compile i x y ls ts r)).eval state = r.eval iv xv yv state.data lvs tvs :=
  (compile_correct _ hb).trans (Shared.compile_read_correct r hi hx hy hl ht)

end LocalRTL
end IRComparison.Circuit.Shared
