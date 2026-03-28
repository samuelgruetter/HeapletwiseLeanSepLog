import HeapletwiseLeanSepLog.DisjointUnion

/-!
Concrete tests for `MMap.subtract` on maps from `UInt32` to `UInt8`.
All lemmas are proved by reflexivity (kernel reduction).
-/

private def m123 : Std.ExtHashMap UInt32 UInt8 :=
  .ofList [(1, 10), (2, 20), (3, 30)]

private def m12 : Std.ExtHashMap UInt32 UInt8 :=
  .ofList [(1, 10), (2, 20)]

private def m1 : Std.ExtHashMap UInt32 UInt8 :=
  .ofList [(1, 10)]

private def mm123 : MMap UInt32 UInt8 := .some m123
private def mm12  : MMap UInt32 UInt8 := .some m12
private def mm1   : MMap UInt32 UInt8 := .some m1

/-- Subtracting from the error sentinel propagates `none`. -/
theorem subtract_none_left :
    (MMap.none (α := UInt32) (β := UInt8)).subtract mm12 = .none := rfl

/-- Subtracting the error sentinel propagates `none`. -/
theorem subtract_none_right :
    mm123.subtract .none = .none := rfl

/-- When `m2` is not a sub-map of `m1`, `subtract` returns `none`.
    Here `mm12` has key 2 but `mm1` does not. -/
theorem subtract_not_submap :
    mm12.subtract mm1 = .none := by rfl

/-- When `m2` is a sub-map of `m1`, `subtract` returns `m1 \ m2`.
    `mm12` ⊆ `mm123`, so the result is `mm123` with keys 1 and 2 removed. -/
theorem subtract_submap :
    mm123.subtract mm12 = .some (m123 \ m12) := by rfl

/-- Subtracting a single-key sub-map removes exactly that key. -/
theorem subtract_one_key :
    mm123.subtract mm1 = .some (m123 \ m1) := by rfl

/-- Subtracting a map from itself gives the empty map. -/
theorem subtract_self :
    mm12.subtract mm12 = .some (m12 \ m12) := by rfl

/-- Subtracting the empty map is always a no-op on the key set. -/
theorem subtract_empty :
    mm123.subtract (.some .empty) = .some (m123 \ .empty) := by rfl
