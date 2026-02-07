/-!
A first effect-row representation for Klean.

This is intentionally simple: a row is an ordered spine of effect types.
Normalization and canonical equivalence are planned in later iterations.
-/

namespace Klean
namespace Kernel

/-- A syntactic effect-row representation used by the kernel layer. -/
inductive Row where
  /-- Empty effect row. -/
  | empty : Row
  /-- Add one effect type to the front of a row. -/
  | cons (effect : Type) (tail : Row) : Row

infixr:67 " ::ᵣ " => Row.cons

namespace Row

/-- Concatenate two effect rows. -/
def append : Row → Row → Row
  | .empty, rhs => rhs
  | .cons eff tl, rhs => .cons eff (append tl rhs)

instance : Append Row where
  append := append

/-- A row containing exactly one effect. -/
def singleton (effect : Type) : Row :=
  .cons effect .empty

/-- Propositional membership of an effect in a row. -/
inductive Contains (effect : Type) : Row → Prop where
  /-- Membership at the head position. -/
  | here {tail} : Contains effect (.cons effect tail)
  /-- Membership in the tail. -/
  | there {head tail} : Contains effect tail → Contains effect (.cons head tail)

/-- If an effect is in `lhs`, it is also in `lhs ++ rhs`. -/
theorem contains_append_left {effect : Type} {lhs rhs : Row} :
    Contains effect lhs → Contains effect (lhs ++ rhs) := by
  induction lhs with
  | empty =>
      intro h
      cases h
  | cons _ tl ih =>
      intro h
      cases h with
      | here =>
          exact Contains.here
      | there htl =>
          exact Contains.there (ih htl)

/-- If an effect is in `rhs`, it is also in `lhs ++ rhs`. -/
theorem contains_append_right {effect : Type} {lhs rhs : Row} :
    Contains effect rhs → Contains effect (lhs ++ rhs) := by
  induction lhs with
  | empty =>
      intro h
      simpa [HAppend.hAppend, Append.append, Row.append] using h
  | cons _ tl ih =>
      intro h
      exact Contains.there (ih h)

/-- Split membership in `lhs ++ rhs` into membership in `lhs` or `rhs`. -/
theorem contains_append_elim {effect : Type} {lhs rhs : Row} :
    Contains effect (lhs ++ rhs) → (Contains effect lhs ∨ Contains effect rhs) := by
  induction lhs with
  | empty =>
      intro h
      exact Or.inr (by simpa [HAppend.hAppend, Append.append, Row.append] using h)
  | cons _ tl ih =>
      intro h
      cases h with
      | here =>
          exact Or.inl Contains.here
      | there htl =>
          cases ih htl with
          | inl hleft =>
              exact Or.inl (Contains.there hleft)
          | inr hright =>
              exact Or.inr hright

/-- Membership characterization for row append. -/
theorem contains_append_iff {effect : Type} {lhs rhs : Row} :
    Contains effect (lhs ++ rhs) ↔ (Contains effect lhs ∨ Contains effect rhs) := by
  constructor
  · exact contains_append_elim
  · intro h
    cases h with
    | inl hleft =>
        exact contains_append_left (rhs := rhs) hleft
    | inr hright =>
        exact contains_append_right (lhs := lhs) hright

/--
Semantic row equivalence: two rows are equivalent if they have the same
effect membership for every effect type.
-/
def SemEq (lhs rhs : Row) : Prop :=
  ∀ {effect : Type}, Contains effect lhs ↔ Contains effect rhs

infix:50 " ≈ " => SemEq

theorem semEq_refl (row : Row) : row ≈ row := by
  intro effect
  exact Iff.rfl

theorem semEq_symm {lhs rhs : Row} : lhs ≈ rhs → rhs ≈ lhs := by
  intro h effect
  exact (h (effect := effect)).symm

theorem semEq_trans {a b c : Row} : a ≈ b → b ≈ c → a ≈ c := by
  intro hab hbc effect
  exact Iff.trans (hab (effect := effect)) (hbc (effect := effect))

/--
Append is commutative at semantic level (membership), even though row syntax is
ordered.
-/
theorem semEq_append_comm (lhs rhs : Row) : (lhs ++ rhs) ≈ (rhs ++ lhs) := by
  intro effect
  constructor
  · intro h
    cases contains_append_elim (lhs := lhs) (rhs := rhs) h with
    | inl hleft =>
        exact contains_append_right (lhs := rhs) hleft
    | inr hright =>
        exact contains_append_left (rhs := lhs) hright
  · intro h
    cases contains_append_elim (lhs := rhs) (rhs := lhs) h with
    | inl hleft =>
        exact contains_append_right (lhs := lhs) hleft
    | inr hright =>
        exact contains_append_left (rhs := rhs) hright

/-- Append is idempotent at semantic level. -/
theorem semEq_append_idem (row : Row) : (row ++ row) ≈ row := by
  intro effect
  constructor
  · intro h
    cases contains_append_elim (lhs := row) (rhs := row) h with
    | inl hleft => exact hleft
    | inr hright => exact hright
  · intro h
    exact contains_append_left (rhs := row) h

/-- Syntactic associativity of row append. -/
theorem append_assoc (a b c : Row) : (a ++ b) ++ c = a ++ (b ++ c) := by
  induction a with
  | empty =>
      rfl
  | cons eff tl ih =>
      exact congrArg (Row.cons eff) ih

/-- Semantic congruence: replacing the left append operand by an equivalent row. -/
theorem semEq_append_congr_left {lhs1 lhs2 rhs : Row} :
    lhs1 ≈ lhs2 → (lhs1 ++ rhs) ≈ (lhs2 ++ rhs) := by
  intro h effect
  constructor
  · intro hm
    have hsplit := (contains_append_iff (lhs := lhs1) (rhs := rhs)).1 hm
    cases hsplit with
    | inl hleft =>
        exact (contains_append_iff (lhs := lhs2) (rhs := rhs)).2 (Or.inl ((h (effect := effect)).1 hleft))
    | inr hright =>
        exact (contains_append_iff (lhs := lhs2) (rhs := rhs)).2 (Or.inr hright)
  · intro hm
    have hsplit := (contains_append_iff (lhs := lhs2) (rhs := rhs)).1 hm
    cases hsplit with
    | inl hleft =>
        exact (contains_append_iff (lhs := lhs1) (rhs := rhs)).2 (Or.inl ((h (effect := effect)).2 hleft))
    | inr hright =>
        exact (contains_append_iff (lhs := lhs1) (rhs := rhs)).2 (Or.inr hright)

/-- Semantic congruence: replacing the right append operand by an equivalent row. -/
theorem semEq_append_congr_right {lhs rhs1 rhs2 : Row} :
    rhs1 ≈ rhs2 → (lhs ++ rhs1) ≈ (lhs ++ rhs2) := by
  intro h effect
  constructor
  · intro hm
    have hsplit := (contains_append_iff (lhs := lhs) (rhs := rhs1)).1 hm
    cases hsplit with
    | inl hleft =>
        exact (contains_append_iff (lhs := lhs) (rhs := rhs2)).2 (Or.inl hleft)
    | inr hright =>
        exact (contains_append_iff (lhs := lhs) (rhs := rhs2)).2 (Or.inr ((h (effect := effect)).1 hright))
  · intro hm
    have hsplit := (contains_append_iff (lhs := lhs) (rhs := rhs2)).1 hm
    cases hsplit with
    | inl hleft =>
        exact (contains_append_iff (lhs := lhs) (rhs := rhs1)).2 (Or.inl hleft)
    | inr hright =>
        exact (contains_append_iff (lhs := lhs) (rhs := rhs1)).2 (Or.inr ((h (effect := effect)).2 hright))

/-- Semantic associativity of append follows from syntactic associativity. -/
theorem semEq_append_assoc (a b c : Row) : ((a ++ b) ++ c) ≈ (a ++ (b ++ c)) := by
  intro effect
  constructor
  · intro h
    simpa [append_assoc a b c] using h
  · intro h
    simpa [append_assoc a b c] using h

end Row
end Kernel
end Klean
