import IRComparison.Circuit.SystemVerilog.Arithmetic

namespace IRComparison.Circuit.SystemVerilog

/-- Pending nonblocking writes. Values are raw unsigned bit patterns; each
read obtains its signedness from the declaration in the old environment. -/
structure Store where
  scalar : Name → Option Int
  cell : Name → Nat → Option Int

def Environment.store (env : Environment) : Store := ⟨env.scalar,env.cell⟩

def Store.setScalar (s : Store) (name : Name) (value : Int) : Store :=
  {s with scalar := fun n => if n = name then some value else s.scalar n}

def Store.setCell (s : Store) (name : Name) (address : Nat) (value : Int) : Store :=
  {s with cell := fun n j => if n = name ∧ j = address then some value else s.cell n j}

/-- A fixed loop's local variable is unsigned and wide enough to represent
its exit value as well as every body index. It is not a circuit register. -/
def Environment.loop (env : Environment) (name : Name) (count iteration : Nat) : Environment :=
  {env with
    type := (fun n => if n = name then ⟨bits count,false⟩ else env.type n)
    scalar := fun n => if n = name then some iteration else env.scalar n}

def Destination.write (target : Destination) (env : Environment) (value : Expr) (pending : Store) : Option Store := do
  match target with
  | .reference n =>
      let v ← value.assignment env (env.type n).width
      return pending.setScalar n v.toNat
  | .index n addressTerm =>
      let j := (← addressTerm.eval env none).integer
      if j < 0 then none else
        -- Undeclared/out-of-bank targets do not acquire new storage.
        let _ ← env.cell n j.toNat
        let v ← value.assignment env (env.type n).width
        return pending.setCell n j.toNat v.toNat

/-- Concrete clocked semantics of the generated two-state subset. All RHSs
see `old`; sequential statement evaluation changes only pending NBA writes.
The sole blocking updates are the local counters of fixed elaboration loops. -/
def Statement.eval (old : Environment) : Statement → Store → Option Store
  | .skip,pending => some pending
  | .assign target value,pending => target.write old value pending
  | .seq first second,pending => do second.eval old (← first.eval old pending)
  | .branch condition yes no,pending => do
      if (← condition.eval old none).integer != 0 then yes.eval old pending else no.eval old pending
  | .forRange loopVar count body,pending =>
      (List.range count).foldlM (fun writes iteration => body.eval (old.loop loopVar count iteration) writes) pending

theorem Statement.seq_eval (old : Environment) (a b : Statement) (pending : Store) :
    (Statement.seq a b).eval old pending = (a.eval old pending).bind (b.eval old) := rfl

theorem loop_counter_fits (inside : iteration ≤ count) :
    (BitVec.ofNat (bits count) iteration).toNat = iteration := by
  have h := bits_fits count
  simp only [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

theorem loop_reference_eval (old : Environment) (name : Name) (inside : iteration ≤ count) :
    (Expr.reference name).eval (old.loop name count iteration) none =
      some (Value.ofInt ⟨bits count,false⟩ iteration) := by
  have fits := loop_counter_fits inside
  simp [Expr.eval,Expr.type,Environment.loop,IntegralType.context,Value.inContext,Value.ofInt,
    BitVec.toNat_ofInt,Int.emod_eq_of_lt (by omega : (0:Int) ≤ iteration)
      (show (iteration : Int) < 2^bits count from by exact_mod_cast (Nat.lt_of_le_of_lt inside (bits_fits count)))]
  rw [if_pos rfl]

/-- Later NBA assignments replace an earlier pending write, but their RHS
still reads the pre-edge environment. This is the distinction needed by
in-place FIFO shifts. -/
theorem scalar_nonblocking (env : Environment) (pending : Store) (name : Name)
    (first second : Expr) (x y : BitVec (env.type name).width)
    (hf : first.assignment env (env.type name).width = some x)
    (hs : second.assignment env (env.type name).width = some y) :
    (Statement.seq (.assign (.reference name) first) (.assign (.reference name) second)).eval env pending =
      some (pending.setScalar name y.toNat) := by
  simp only [Statement.eval,Destination.write,hf,hs,bind,Option.bind,pure]
  congr 1
  unfold Store.setScalar
  congr 1
  funext n
  split <;> simp_all

end IRComparison.Circuit.SystemVerilog
