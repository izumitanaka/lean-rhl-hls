import IRComparison.Circuit.CommandWordRanges
import IRComparison.Circuit.RangeMonotone

namespace IRComparison.Circuit

/-- Only the already allocated wire declarations can affect this expression's
computed range. This concerns range inference, not source-state semantics. -/
def RangeScoped (limit : Nat) (e : Expr) : Prop :=
  ∀ (a b : Nat → Interval), (∀ n, n < limit → a n = b n) → range a e = range b e

namespace RangeScoped

theorem fail : RangeScoped n .fail := by intro a b same; rfl
theorem lit : RangeScoped n (.lit k) := by intro a b same; rfl
theorem reg : RangeScoped n (.reg k) := by intro a b same; rfl
theorem memory : RangeScoped n (.memory a j) := by intro a b same; rfl
theorem wire (valid : k < n) : RangeScoped n (.wire k) := by intro a b same; exact same k valid

theorem bin (ha : RangeScoped n a) (hb : RangeScoped n b) : RangeScoped n (.bin op a b) := by
  intro small big same
  simp only [range]
  split
  · rfl
  · rw [ha small big same,hb small big same]

theorem natIndex (h : RangeScoped n e) : RangeScoped n (.natIndex e) := by
  intro a b same
  change (⟨max 0 (range a e).lo,max 0 (range a e).hi⟩ : Interval) = _
  rw [h a b same]
  rfl

theorem wrap32 : RangeScoped n (.wrap32 e) := by intro a b same; rfl

theorem select (ha : RangeScoped n a) (hb : RangeScoped n b) : RangeScoped n (.select c a b) := by
  intro small big same
  change union (range small a) (range small b) = _
  rw [ha small big same,hb small big same]
  rfl

theorem seq (hb : RangeScoped n b) : RangeScoped n (.seq a b) := hb

theorem mono (h : RangeScoped n e) (le : n ≤ m) : RangeScoped m e :=
  fun a b same => h a b (fun k hk => same k (Nat.lt_of_lt_of_le hk le))

theorem lookup (scope : ∀ e ∈ es, RangeScoped n e) : RangeScoped n (Circuit.lookup es k) := by
  cases found : es[k]? with
  | none => simpa [Circuit.lookup,found] using (RangeScoped.fail (n:=n))
  | some e => simpa [Circuit.lookup,found] using scope e (List.mem_of_getElem? found)

theorem value (v : HybridIR.Value) (hi : RangeScoped n i) (hx : RangeScoped n x) (hy : RangeScoped n y)
    (locals : ∀ e ∈ ls, RangeScoped n e) (temps : ∀ e ∈ ts, RangeScoped n e) :
    RangeScoped n (Circuit.value i x y ls ts v) := by
  induction v with
  | lit => exact .lit
  | index => exact hi
  | left => exact hx
  | right => exact hy
  | «local» => exact lookup locals
  | temp => exact lookup temps
  | natIndex _ ih => exact ih.natIndex
  | wrap32 _ _ => exact .wrap32
  | add _ _ a b | sub _ _ a b | mul _ _ a b | div _ _ a b => exact .bin a b

theorem read (e : HybridIR.ReadCode) (hi : RangeScoped n i) (hx : RangeScoped n x) (hy : RangeScoped n y)
    (locals : ∀ e ∈ ls, RangeScoped n e) (temps : ∀ e ∈ ts, RangeScoped n e) :
    RangeScoped n (Circuit.read i x y ls ts e) := by
  induction e generalizing ts with
  | pure v => exact value v hi hx hy locals temps
  | register => exact .reg
  | memory => exact .memory
  | bind a b ha hb =>
    apply RangeScoped.seq
    apply hb
    intro e member
    rcases List.mem_cons.mp member with rfl | member
    · exact ha temps
    · exact temps e member
  | branch _ _ _ a b => exact .select (a temps) (b temps)

theorem context_read (ctx : CommandWordRanges.Context b slots types) (hi : RangeScoped b.wires.size i)
    (e : HybridIR.ReadCode) :
    RangeScoped b.wires.size (Circuit.read i (.wire 0) (.wire 1) (slots.map Expr.wire) [] e) := by
  apply read e hi (.wire (by have := ctx.inputs; omega)) (.wire (by have := ctx.inputs; omega))
  · intro e member
    obtain ⟨slot,hm,rfl⟩ := List.mem_map.mp member
    exact .wire (ctx.scopedSlots slot hm)
  · simp

end RangeScoped

theorem RangeScoped.frame_range {b : Build} (scope : RangeScoped b.wires.size e) :
    range (CommandWordRanges.wires b) e = range (Frame.get b.wires.toList) e := by
  apply scope
  intro n valid
  simp [CommandWordRanges.wires,Frame.get,Array.getElem?_eq_getElem valid]

variable {b final : Build} {frame : Frame}

theorem RangeScoped.exprRange_extend {before after : Build}
    (scope : RangeScoped before.wires.size e) (kept : WireAllocation.Extends before after) :
    before.exprRange e = after.exprRange e := by
  apply scope
  intro n valid
  simp only [kept.get valid]

theorem WireAllocation.fresh_bound {b final : Build}
    (kept : Extends (b.addWire r) final) :
    (Frame.get final.wires.toList) b.wires.size = ⟨min 0 r.lo,max 0 r.hi⟩ := by
  have newSlot := kept.get (n:=b.wires.size) (by simp [Build.addWire])
  simp only [Frame.get,Array.getElem?_toList,← newSlot,Build.addWire,Array.getElem?_push_eq,Option.getD_some]

theorem WireAllocation.fresh_valid {b final : Build}
    (kept : Extends (b.addWire r) final) : b.wires.size < final.wires.toList.length := by
  have := kept.size
  simp only [Build.addWire,Array.size_push,Array.length_toList] at *
  omega

/-- The width chosen for a capture remains sufficient after every later
allocation. This also covers unwrapped integer task indices and loop bounds. -/
theorem capture_range (scope : RangeScoped b.wires.size e)
    (kept : WireAllocation.Extends (b.addWire (b.exprRange e)) final) :
    (range (Frame.get final.wires.toList) e).Inside ((Frame.get final.wires.toList) b.wires.size) := by
  have all := (CommandWordRanges.addWire_prefix b (b.exprRange e)).trans kept
  have equalRange : range (fun n => b.wires[n]?.getD wordRange) e = range (Frame.get final.wires.toList) e := by
    apply scope
    intro n hn
    have found := all.get hn
    have valid : n < final.wires.size := Nat.lt_of_lt_of_le hn all.size
    simp only [Frame.get,Array.getElem?_toList,found,Array.getElem?_eq_getElem valid,Option.getD_some]
  have slotValue := WireAllocation.fresh_bound kept
  rw [slotValue,← equalRange]
  change min 0 (b.exprRange e).lo ≤ (b.exprRange e).lo ∧ (b.exprRange e).hi ≤ max 0 (b.exprRange e).hi
  exact ⟨Int.min_le_right _ _,Int.le_max_right _ _⟩

theorem transfer_capture (scope : RangeScoped b.wires.size e)
    (kept : WireAllocation.Extends (b.addWire (b.exprRange e)) final)
    (fits : frame.within final.wires.toList = true) (next : Nat) :
    ∃ edges, transfer frame (.wire b.wires.size e next) = .ok edges ∧
      ∀ edge ∈ edges, edge.2.within final.wires.toList = true := by
  apply transfer_wire_inside fits
  · have len := Frame.within_length fits
    have growth := kept.size
    simp only [Build.addWire,Array.size_push,Array.length_toList] at growth len
    omega
  · exact capture_range scope kept

end IRComparison.Circuit
