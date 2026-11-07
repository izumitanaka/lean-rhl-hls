import PaperCore.MemoryLoopCoverage

namespace PaperCore.MemoryFacts
open AccessAnalysis MemoryCoverage

structure Span where
  array : Array
  first : Int
  stride : Int
  count : Nat
  deriving DecidableEq, Repr

def Span.Holds (span : Span) (heap : Heap) : Prop :=
  Covers heap span.array span.first span.stride span.count

def Holds (facts : List Span) (heap : Heap) : Prop := ∀ span ∈ facts, span.Holds heap

theorem preserved (run : SourceExec meaning code initial final) (known : Holds facts initial.memory) :
    Holds facts final.memory := fun span member => covers_preserved run (known span member)

structure Result (classify : Op → Option Arithmetic) (source : Source Op) where
  facts : List Span
  sound : ∀ meaning, ArithmeticSound classify meaning → ∀ {initial final},
    SourceExec meaning source initial final → Holds facts final.memory
  notes : List String := []

def empty (classify : Op → Option Arithmetic) (source : Source Op) (reason : String := "") : Result classify source :=
  ⟨[],by intros; intro span member; simp at member,if reason = "" then [] else [reason]⟩

/-- Initialization facts come from the semantics of completed code, not from
executing a concrete test input or trusting a proposed access pattern. -/
def infer (classify : Op → Option Arithmetic) (source : Source Op) : Result classify source :=
  match source with
  | .seq a b =>
    let left := infer classify a
    let right := infer classify b
    ⟨left.facts ++ right.facts,by
      intro meaning ops initial final run span member
      cases run with
      | seq first second =>
        rcases List.mem_append.mp member with hl | hr
        · exact preserved second (left.sound meaning ops first) span hl
        · exact right.sound meaning ops second span hr,left.notes ++ right.notes⟩
  | .branch condition a b =>
    let yes := infer classify a
    let no := infer classify b
    ⟨yes.facts.filter (fun span => decide (span ∈ no.facts)),by
      intro meaning ops initial final run span member
      have selected := List.mem_filter.mp member
      cases run with
      | ifTrue condition nonzero body => exact yes.sound meaning ops body span selected.1
      | ifFalse condition body => exact no.sound meaning ops body span (by simpa using selected.2),yes.notes ++ no.notes⟩
  | .kernel body =>
    let inside := infer classify body
    ⟨inside.facts,by intro meaning ops initial final run; cases run with
      | kernel body => exact inside.sound meaning ops body,inside.notes⟩
  | .loop counter (.num start) stop step body =>
    match analysis : analyze classify (Env.initial counter) body with
    | .error reason => empty classify _ ("initialization-analysis:" ++ reason)
    | .ok summary =>
      match summary.env counter with
      | none => empty classify _ "initialization-counter-unknown"
      | some affine =>
        let delta := affine.offset+step
        if known : summary.env counter = some ⟨1,delta-step⟩ then
        if nonzero : delta ≠ 0 then
          let trips := ((stop-start)/delta).toNat
          if endpoint : stop = start+(trips:Int)*delta then
            ⟨summary.accesses.map (fun e => ⟨e.array,e.index.eval start,e.index.scale*delta,trips⟩),by
              intro meaning ops initial final run span member
              obtain ⟨event,he,rfl⟩ := List.mem_map.mp member
              exact loop_covers ops analysis known nonzero he endpoint run,[]⟩
          else empty classify _ "initialization-endpoint-not-reached"
        else empty classify _ "initialization-zero-net-step"
        else empty classify _ "initialization-counter-not-affine"
  | other => empty classify other "initialization-no-summary"

/-- A constant-size description of a contiguous initialized interval. -/
def Span.interval (span : Span) : Option (Int × Int) :=
  if span.stride = 1 then some (span.first,span.first+(span.count:Int))
  else if span.stride = -1 then some (span.first-(span.count:Int)+1,span.first+1)
  else none

theorem Span.interval_sound {span : Span} (known : span.Holds heap) (found : span.interval = some (low,high))
    (lo : low ≤ index) (hi : index < high) : Defined heap span.array index := by
  unfold Span.interval at found
  split at found
  · rename_i stride
    simp only [Option.some.injEq,Prod.mk.injEq] at found
    obtain ⟨rfl,rfl⟩ := found
    have point := known (index-span.first).toNat (by omega)
    have address : span.first+((index-span.first).toNat:Int)*span.stride = index := by
      rw [stride,Int.toNat_of_nonneg (by omega : 0 ≤ index-span.first)]; omega
    simpa only [address] using point
  · split at found
    · rename_i stride
      simp only [Option.some.injEq,Prod.mk.injEq] at found
      obtain ⟨rfl,rfl⟩ := found
      have point := known (span.first-index).toNat (by omega)
      have address : span.first+((span.first-index).toNat:Int)*span.stride = index := by
        rw [stride,Int.toNat_of_nonneg (by omega : 0 ≤ span.first-index)]; omega
      simpa only [address] using point
    · simp at found

theorem Span.interval_contains {span : Span} (found : span.interval = some (low,high)) (n : Nat) (bound : n < span.count) :
    low ≤ span.first+(n:Int)*span.stride ∧ span.first+(n:Int)*span.stride < high := by
  unfold Span.interval at found
  split at found
  · rename_i stride
    simp only [Option.some.injEq,Prod.mk.injEq] at found
    obtain ⟨rfl,rfl⟩ := found
    simp only [stride,Int.mul_one]
    omega
  · split at found
    · rename_i stride
      simp only [Option.some.injEq,Prod.mk.injEq] at found
      obtain ⟨rfl,rfl⟩ := found
      simp only [stride,Int.mul_neg,Int.mul_one]
      omega
    · simp at found

structure Certificate (facts : List Span) (needed : Span) : Type where
  sound : ∀ heap, Holds facts heap → needed.Holds heap

/-- No enumeration proportional to array size. Failure to prove coverage is
not permission to prefetch an undefined cell. -/
def certify (facts : List Span) (needed : Span) : Option (Certificate facts needed) :=
  if zero : needed.count = 0 then some ⟨by intro heap known n hn; simp [zero] at hn⟩
  else match requested : needed.interval with
  | none => none
  | some (low,high) =>
    let rec find (remaining : List Span) (included : ∀ span ∈ remaining, span ∈ facts) :
        Option (Certificate facts needed) :=
      match remaining with
      | [] => none
      | span :: rest =>
        match available : span.interval with
        | none => find rest (fun s hs => included s (List.mem_cons_of_mem _ hs))
        | some (lo,hi) =>
          if fits : span.array = needed.array ∧ lo ≤ low ∧ high ≤ hi then
            some ⟨by
              intro heap known n hn
              have bounds := needed.interval_contains requested n hn
              have cell := span.interval_sound (known span (included span (by simp))) available
                (Int.le_trans fits.2.1 bounds.1) (Int.lt_of_lt_of_le bounds.2 fits.2.2)
              simpa only [fits.1] using cell⟩
          else find rest (fun s hs => included s (List.mem_cons_of_mem _ hs))
    find facts (fun _ h => h)

#print axioms infer
#print axioms certify
end PaperCore.MemoryFacts
