import PaperCore.SMT.SMT
namespace PaperCore.Model

/-- Ordered values of p0,p1,... are mapped to the exact parameter schema used by the query. -/
def decode (schema : List String) (values : List Int) : Option (List (String × Int)) :=
  if schema.Nodup ∧ schema.length = values.length then some (schema.zip values) else none

 theorem decode_shape {schema : List String} {values : List Int} {bindings : List (String × Int)}
    (h : decode schema values = some bindings) :
    schema.Nodup ∧ schema.length = values.length ∧ bindings = schema.zip values := by
  unfold decode at h
  split at h
  next hc => exact ⟨hc.1,hc.2,(Option.some.inj h).symm⟩
  next => contradiction

 theorem lookup_zip_at (schema : List String) (values : List Int)
    (hn : schema.Nodup) (hl : schema.length = values.length)
    (i : Nat) (hi : i < schema.length) :
    (schema.zip values).lookup schema[i] = values[i]? := by
  induction schema generalizing values i with
  | nil => simp at hi
  | cons key keys ih =>
    cases values with
    | nil => simp at hl
    | cons v vs =>
      have hkeys : keys.Nodup := (List.nodup_cons.mp hn).2
      have hnot : key ∉ keys := (List.nodup_cons.mp hn).1
      have hlen : keys.length = vs.length := by simpa using hl
      cases i with
      | zero => simp
      | succ i =>
        have hi' : i < keys.length := by simpa using hi
        have hne : keys[i] ≠ key := by
          intro he
          exact hnot (he ▸ List.getElem_mem hi')
        have hb : (keys[i] == key) = false := beq_eq_false_iff_ne.mpr hne
        simpa [List.lookup_cons, hb] using ih vs hkeys hlen i hi'

/-- The actual named lookup used by the transformer returns the corresponding solver value. -/
theorem decode_correct {schema : List String} {values : List Int} {bindings : List (String × Int)}
    (h : decode schema values = some bindings) (i : Nat) (hi : i < schema.length) :
    bindings.lookup schema[i] = values[i]? := by
  obtain ⟨hn,hl,rfl⟩ := decode_shape h
  exact lookup_zip_at schema values hn hl i hi

/-- Missing and additional values are rejected; no default-zero model fields are introduced. -/
theorem wrong_length_rejected (schema : List String) (values : List Int)
    (h : schema.length ≠ values.length) : decode schema values = none := by
  simp [decode,h]

theorem duplicate_schema_rejected (schema : List String) (values : List Int)
    (h : ¬schema.Nodup) : decode schema values = none := by
  simp [decode,h]

#print axioms decode_correct

theorem lookup_zip_index (schema : List String) (values : List Int)
    (hl : schema.length = values.length) (x : String) :
    (schema.zip values).lookup x = values[schema.idxOf x]? := by
  induction schema generalizing values with
  | nil => cases values <;> simp_all
  | cons key keys ih =>
    cases values with
    | nil => simp at hl
    | cons v vs =>
      have hlen : keys.length = vs.length := by simpa using hl
      by_cases he : x=key
      · subst x; simp
      · have hb : (x==key)=false := beq_eq_false_iff_ne.mpr he
        have hb' : (key==x)=false := beq_eq_false_iff_ne.mpr (Ne.symm he)
        simpa [List.lookup_cons,List.idxOf_cons,hb,hb'] using ih vs hlen

theorem decode_assignment {schema : List String} {values : List Int} {bindings : List (String × Int)}
    (h : decode schema values = some bindings) :
    (fun x => (bindings.lookup x).getD 0) =
      (fun x => (values[schema.idxOf x]?).getD 0) := by
  obtain ⟨_,hl,rfl⟩ := decode_shape h
  funext x
  rw [lookup_zip_index schema values hl x]

#print axioms decode_assignment
end PaperCore.Model
