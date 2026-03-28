import Std.Data.ExtHashMap

namespace Std.ExtHashMap

variable {α : Type u} {β : Type v} [BEq α] [Hashable α]

/-- Two hash maps are disjoint if they share no keys. -/
def disjoint (m₁ m₂ : Std.ExtHashMap α β) : Prop :=
  ∀ k : α, ¬(m₁.contains k ∧ m₂.contains k)

/-- Boolean test for map disjointness: returns `true` iff the maps share no keys. -/
def isDisjoint (m₁ m₂ : Std.ExtHashMap α β) : Bool :=
  m₁.fold (fun acc k _ => acc && !m₂.contains k) true

/-- `isDisjoint m₁ m₂ = true` iff `m₁` and `m₂` are disjoint. -/
theorem isDisjoint_iff (m₁ m₂ : Std.ExtHashMap α β) :
    isDisjoint m₁ m₂ = true ↔ disjoint m₁ m₂ := by
  sorry

/-- Decidability of `disjoint`, witnessed by `isDisjoint`. -/
instance instDecidableDisjoint (m₁ m₂ : Std.ExtHashMap α β) :
    Decidable (disjoint m₁ m₂) :=
  decidable_of_iff (isDisjoint m₁ m₂ = true) (isDisjoint_iff m₁ m₂)

end Std.ExtHashMap
