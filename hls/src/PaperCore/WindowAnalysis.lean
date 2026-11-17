import PaperCore.LoopAnalysis

namespace PaperCore.WindowAnalysis
open AccessAnalysis LoopAnalysis

/-- These are analysis candidates, not permission to preload every cell in
    the interval. Coverage/definedness and transformation VCs remain required. -/
structure Window where
  array : Array
  scale : Int
  low : Int
  high : Int
  offsets : List Int
  deriving Repr, DecidableEq

def bounds : List Int → Option (Int × Int)
  | [] => none
  | x :: xs =>
    match bounds xs with
    | none => some (x,x)
    | some (low,high) => some (min x low,max x high)

theorem bounds_cover (success : bounds xs = some (low,high)) (member : value ∈ xs) :
    low ≤ value ∧ value ≤ high := by
  induction xs generalizing low high with
  | nil => simp [bounds] at success
  | cons x xs ih =>
    cases hb : bounds xs with
    | none =>
      have empty : xs = [] := by
        cases xs with
        | nil => rfl
        | cons y ys => cases hy : bounds ys <;> simp [bounds,hy] at hb
      subst xs
      simp [bounds] at success
      obtain ⟨rfl,rfl⟩ := success
      simp only [List.mem_singleton] at member
      subst value
      exact ⟨Int.le_refl _,Int.le_refl _⟩
    | some pair =>
      obtain ⟨lo,hi⟩ := pair
      simp [bounds,hb] at success
      obtain ⟨rfl,rfl⟩ := success
      rcases List.mem_cons.mp member with same | tail
      · subst value; omega
      · have covered := ih hb tail
        omega

def selected (array : Array) (accesses : List SymbolicAccess) : List SymbolicAccess :=
  accesses.filter (fun a => a.array == array)

def infer (array : Array) (accesses : List SymbolicAccess) : Except String Window :=
  match selected array accesses with
  | [] => .error "no-access-to-array"
  | first :: rest =>
    if (first :: rest).any (fun a => a.direction == .write) then
      .error "window-analysis-read-write-array-not-yet-supported"
    else if !(rest.all (fun a => a.index.scale == first.index.scale)) then
      .error "window-analysis-nonuniform-index-scale"
    else
      let offsets := (first :: rest).map (fun a => a.index.offset)
      match bounds offsets with
      | none => .error "internal-empty-window"
      | some (low,high) => .ok ⟨array,first.index.scale,low,high,offsets⟩

structure Report where
  array : Array
  result : Except String Window
  deriving Repr

def inferAll (accesses : List SymbolicAccess) : List Report :=
  ((accesses.map (·.array)).eraseDups).map (fun a => ⟨a,infer a accesses⟩)

/-- Every access to an accepted window's array is a read at the reported
    scale and inside its offset interval. Holes are not declared initialized. -/
theorem infer_sound (success : infer array accesses = .ok window)
    (member : access ∈ accesses) (sameArray : access.array = array) :
    window.array = array ∧ access.direction = .read ∧ access.index.scale = window.scale ∧
      window.low ≤ access.index.offset ∧ access.index.offset ≤ window.high := by
  have chosen : access ∈ selected array accesses := by simp [selected,member,sameArray]
  unfold infer at success
  cases hs : selected array accesses with
  | nil => simp [hs] at chosen
  | cons first rest =>
    simp only [hs] at success chosen
    split at success
    next writes => contradiction
    next noWrites =>
      split at success
      next nonuniform => contradiction
      next uniform =>
        cases hb : bounds ((first :: rest).map (fun a => a.index.offset)) with
        | none =>
          simp only [List.map_cons] at hb
          simp [hb] at success
        | some pair =>
          obtain ⟨lo,hi⟩ := pair
          simp only [List.map_cons] at hb
          simp [hb] at success
          subst window
          have allRead : access.direction ≠ .write := by
            intro write
            have any : (first :: rest).any (fun a => a.direction == .write) = true :=
              List.any_eq_true.mpr ⟨access,chosen,by simp [write]⟩
            exact noWrites any
          have read : access.direction = .read := by cases hd : access.direction <;> simp_all
          have scales : rest.all (fun a => a.index.scale == first.index.scale) = true := by
            simpa using uniform
          have scale : access.index.scale = first.index.scale := by
            rcases List.mem_cons.mp chosen with eq | tail
            · subst access; rfl
            · exact beq_iff_eq.mp (List.all_eq_true.mp scales access tail)
          have offsetMember : access.index.offset ∈ (first :: rest).map (fun a => a.index.offset) :=
            List.mem_map.mpr ⟨access,chosen,rfl⟩
          have covered := bounds_cover hb (by simpa only [List.map_cons] using offsetMember)
          exact ⟨rfl,read,scale,covered⟩

#print axioms bounds_cover
theorem runtime_covered (success : infer array accesses = .ok window)
    (member : observed ∈ accesses.map (SymbolicAccess.eval counter)) (same : observed.array = array) :
    observed.direction = .read ∧ window.scale * counter + window.low ≤ observed.index ∧
      observed.index ≤ window.scale * counter + window.high := by
  obtain ⟨access,belongs,rfl⟩ := List.mem_map.mp member
  obtain ⟨arrayEq,read,scale,low,high⟩ := infer_sound success belongs same
  refine ⟨read,?_,?_⟩ <;>
    simp only [SymbolicAccess.eval,Affine.eval,scale] <;> omega

#print axioms infer_sound
#print axioms runtime_covered
end PaperCore.WindowAnalysis
