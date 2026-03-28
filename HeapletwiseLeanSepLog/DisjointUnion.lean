import Std.Data.ExtHashMap

namespace Std.ExtHashMap

variable {α : Type u} {β : Type v} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]

/-- Two hash maps are disjoint if they share no keys. -/
def disjoint (m₁ m₂ : Std.ExtHashMap α β) : Prop :=
  ∀ k : α, ¬(k ∈ m₁ ∧ k ∈ m₂)

/-- Boolean test for map disjointness: returns `true` iff the maps share no keys. -/
def isDisjoint (m₁ m₂ : Std.ExtHashMap α β) : Bool :=
  (m₁ ∩ m₂).isEmpty

/-- `isDisjoint m₁ m₂ = true` iff `m₁` and `m₂` are disjoint. -/
theorem isDisjoint_iff (m₁ m₂ : Std.ExtHashMap α β) :
    isDisjoint m₁ m₂ = true ↔ disjoint m₁ m₂ := by
  simp only [isDisjoint, disjoint, isEmpty_inter_iff, not_and]

/-- Decidability of `disjoint`, witnessed by `isDisjoint`. -/
instance instDecidableDisjoint (m₁ m₂ : Std.ExtHashMap α β) :
    Decidable (disjoint m₁ m₂) :=
  match h : isDisjoint m₁ m₂ with
  | true  => isTrue  ((isDisjoint_iff m₁ m₂).mp h)
  | false => isFalse (mt (isDisjoint_iff m₁ m₂).mpr (by simp [h]))

end Std.ExtHashMap
