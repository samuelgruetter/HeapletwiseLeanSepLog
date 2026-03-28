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

/-- Merges two maps when they are disjoint, returning `none` if their
    keys overlap. Mirrors the Rocq `du` function. -/
def disjointUnion (m₁ m₂ : Std.ExtHashMap α β) : Option (Std.ExtHashMap α β) :=
  if isDisjoint m₁ m₂ then some (m₁ ∪ m₂) else none

end Std.ExtHashMap

/-- A "maybe-map": either a concrete hash map or an overlap sentinel,
    isomorphic to `Option (Std.ExtHashMap α β)`. -/
inductive MMap (α : Type u) (β : Type v) [BEq α] [Hashable α]
    [EquivBEq α] [LawfulHashable α] where
  | none : MMap α β
  | some : Std.ExtHashMap α β → MMap α β

namespace MMap

variable {α : Type u} {β : Type v} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]

/-- Disjoint union of two `MMap`s. Propagates `none` and returns
    `none` whenever the underlying maps have overlapping keys. -/
def disjointUnion (m₁ m₂ : MMap α β) : MMap α β :=
  match m₁, m₂ with
  | none,   _      => none
  | _,      none   => none
  | some a, some b =>
    match Std.ExtHashMap.disjointUnion a b with
    | .some m => some m
    | .none   => none

end MMap
