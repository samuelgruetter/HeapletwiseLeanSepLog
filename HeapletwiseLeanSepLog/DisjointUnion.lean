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
    keys overlap. -/
def disjointUnion (m₁ m₂ : Std.ExtHashMap α β) : Option (Std.ExtHashMap α β) :=
  if isDisjoint m₁ m₂ then some (m₁ ∪ m₂) else none

/-- `disjoint` is symmetric. -/
theorem disjoint_symm (m₁ m₂ : Std.ExtHashMap α β) :
    disjoint m₁ m₂ ↔ disjoint m₂ m₁ := by
  simp [disjoint, and_comm]

/-- `isDisjoint` is symmetric. -/
theorem isDisjoint_symm (m₁ m₂ : Std.ExtHashMap α β) :
    isDisjoint m₁ m₂ = isDisjoint m₂ m₁ := by
  rw [Bool.eq_iff_iff, isDisjoint_iff, isDisjoint_iff]
  exact disjoint_symm m₁ m₂

/-- Disjointness splits over union on the left. -/
theorem disjoint_union_left (a b c : Std.ExtHashMap α β) :
    disjoint (a ∪ b) c ↔ disjoint a c ∧ disjoint b c := by
  simp only [disjoint, mem_union_iff, not_and, or_imp, forall_and]

/-- `isDisjoint (a ∪ b) c = isDisjoint a c && isDisjoint b c`. -/
theorem isDisjoint_union_left (a b c : Std.ExtHashMap α β) :
    isDisjoint (a ∪ b) c = (isDisjoint a c && isDisjoint b c) := by
  rw [Bool.eq_iff_iff, Bool.and_eq_true, isDisjoint_iff, isDisjoint_iff, isDisjoint_iff,
      disjoint_union_left]

/-- Disjointness splits over union on the right. -/
theorem disjoint_union_right (a b c : Std.ExtHashMap α β) :
    disjoint a (b ∪ c) ↔ disjoint a b ∧ disjoint a c := by
  rw [disjoint_symm, disjoint_union_left, disjoint_symm b, disjoint_symm c]

/-- `isDisjoint a (b ∪ c) = isDisjoint a b && isDisjoint a c`. -/
theorem isDisjoint_union_right (a b c : Std.ExtHashMap α β) :
    isDisjoint a (b ∪ c) = (isDisjoint a b && isDisjoint a c) := by
  rw [Bool.eq_iff_iff, Bool.and_eq_true, isDisjoint_iff, isDisjoint_iff, isDisjoint_iff,
      disjoint_union_right]

/-- Union of hash maps is associative.
    Requires `LawfulBEq α` for the extensionality argument. -/
theorem union_assoc [LawfulBEq α] (a b c : Std.ExtHashMap α β) :
    (a ∪ b) ∪ c = a ∪ (b ∪ c) := by
  ext k
  simp only [getElem?_union, Option.or_assoc]

/-- `m₂` is a sub-map of `m₁`: every `(k, v)` pair of `m₂` is present
    in `m₁` with the same value. -/
def isSubmap [BEq β] (m₁ m₂ : Std.ExtHashMap α β) : Bool :=
  (m₂.filter (fun k v => !(m₁[k]? == some v))).isEmpty

/-- Subtracts `m₂` from `m₁`: if every `(k, v)` pair of `m₂` is found
    in `m₁`, returns `m₁` with those keys removed; otherwise `none`. -/
def subtract [BEq β] (m₁ m₂ : Std.ExtHashMap α β) : Option (Std.ExtHashMap α β) :=
  if isSubmap m₁ m₂ then some (m₁ \ m₂) else none

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

/-- `MMap.disjointUnion` is associative.
    Requires `LawfulBEq α` for `ExtHashMap.union_assoc`. -/
theorem disjointUnion_assoc [LawfulBEq α] (m₁ m₂ m₃ : MMap α β) :
    (m₁.disjointUnion m₂).disjointUnion m₃ =
    m₁.disjointUnion (m₂.disjointUnion m₃) := by
  match m₁, m₂, m₃ with
  -- Cases where a `none` appears: both sides reduce to `none` structurally.
  | none,   _,      _      => rfl
  | some _, none,   _      => rfl
  -- m₃ = none: inner `some a ⊎ some b` may be stuck, so split on isDisjoint a b.
  | some a, some b, none   =>
    simp only [disjointUnion, Std.ExtHashMap.disjointUnion]
    rcases h : Std.ExtHashMap.isDisjoint a b <;> simp_all
  -- Main case: split on all three atomic disjointness predicates.
  | some a, some b, some c =>
    simp only [disjointUnion, Std.ExtHashMap.disjointUnion]
    rcases h12 : Std.ExtHashMap.isDisjoint a b <;>
    rcases h13 : Std.ExtHashMap.isDisjoint a c <;>
    rcases h23 : Std.ExtHashMap.isDisjoint b c <;>
    simp_all [Std.ExtHashMap.isDisjoint_union_left,
              Std.ExtHashMap.isDisjoint_union_right,
              Std.ExtHashMap.union_assoc]

/-- Decidable equality for `MMap`, given decidable equality on values. -/
instance instDecidableEqMMap [LawfulBEq α] [BEq β] [LawfulBEq β] :
    DecidableEq (MMap α β)
  | .none,   .none   => .isTrue rfl
  | .none,   .some _ => .isFalse (fun h => by cases h)
  | .some _, .none   => .isFalse (fun h => by cases h)
  | .some a, .some b =>
    if h : a = b
    then .isTrue (congrArg MMap.some h)
    else .isFalse (fun heq => h (MMap.some.inj heq))

/-- Subtraction on `MMap`s. Propagates the error sentinel `none` and
    returns `none` whenever the underlying subtraction fails. -/
def subtract [BEq β] (m₁ m₂ : MMap α β) : MMap α β :=
  match m₁, m₂ with
  | none,   _      => none
  | _,      none   => none
  | some a, some b =>
    match Std.ExtHashMap.subtract a b with
    | .some m => some m
    | .none   => none

end MMap
