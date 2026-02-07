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
Proof witness that `out` is `src` with one occurrence of `effect` removed.
-/
inductive Remove (effect : Type) : Row → Row → Prop where
  | head {tail : Row} : Remove effect (.cons effect tail) tail
  | tail {head : Type} {tail out : Row} : Remove effect tail out → Remove effect (.cons head tail) (.cons head out)

/-- Membership implies that some one-step removal witness exists. -/
theorem exists_remove_of_contains {effect : Type} {row : Row} :
    Contains effect row → ∃ out, Remove effect row out := by
  intro hContains
  induction hContains with
  | here =>
      exact ⟨_, Remove.head⟩
  | there hTail ih =>
      rcases ih with ⟨out, hRemove⟩
      exact ⟨_, Remove.tail hRemove⟩

/-- A removed row can always be embedded back into the source row. -/
theorem contains_lift_remove {effect other : Type} {src out : Row} :
    Remove effect src out → Contains other out → Contains other src := by
  intro hRemove hOut
  induction hRemove with
  | head =>
      exact Contains.there hOut
  | tail hTail ih =>
      cases hOut with
      | here =>
          exact Contains.here
      | there hOutTail =>
          exact Contains.there (ih hOutTail)

/-- A `Remove` witness guarantees membership of the removed effect in the source row. -/
theorem contains_of_remove {effect : Type} {src out : Row} :
    Remove effect src out → Contains effect src := by
  intro hRemove
  induction hRemove with
  | head =>
      exact Contains.here
  | tail _ ih =>
      exact Contains.there ih

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

/-- Semantic equivalence is stable under adding the same head constructor. -/
theorem semEq_cons_congr {head : Type} {tail1 tail2 : Row} :
    tail1 ≈ tail2 → (Row.cons head tail1) ≈ (Row.cons head tail2) := by
  intro h effect
  constructor
  · intro hm
    cases hm with
    | here =>
        exact Contains.here
    | there hTail =>
        exact Contains.there ((h (effect := effect)).1 hTail)
  · intro hm
    cases hm with
    | here =>
        exact Contains.here
    | there hTail =>
        exact Contains.there ((h (effect := effect)).2 hTail)

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

/--
Any explicit removal witness decomposes a row semantically as:
`src ≈ out ++ [effect]`.
-/
theorem semEq_append_singleton_of_remove {effect : Type} {src out : Row} :
    Remove effect src out → src ≈ (out ++ singleton effect) := by
  intro hRemove
  induction hRemove with
  | @head tail =>
      intro probe
      constructor
      · intro hMem
        cases hMem with
        | here =>
            exact contains_append_right (lhs := tail) (by simpa [singleton] using (Contains.here : Contains effect (singleton effect)))
        | there hTail =>
            exact contains_append_left (rhs := singleton effect) hTail
      · intro hMem
        have hSplit := (contains_append_iff (lhs := tail) (rhs := singleton effect)).1 hMem
        cases hSplit with
        | inl hTail =>
            exact Contains.there hTail
        | inr hSingleton =>
            cases hSingleton with
            | here =>
                exact Contains.here
            | there hImpossible =>
                cases hImpossible
  | @tail head tail out hTail ih =>
      have hCons : (Row.cons head tail) ≈ (Row.cons head (out ++ singleton effect)) := semEq_cons_congr ih
      change (Row.cons head tail) ≈ (Row.cons head (out ++ singleton effect))
      exact hCons

/--
If `effect` is contained in `row`, we can exhibit a row `out` such that
`row` is semantically equivalent to `out ++ [effect]`.
-/
theorem exists_remove_decomposition {effect : Type} {row : Row} :
    Contains effect row → ∃ out, Remove effect row out ∧ row ≈ (out ++ singleton effect) := by
  intro hContains
  rcases exists_remove_of_contains hContains with ⟨out, hRemove⟩
  exact ⟨out, hRemove, semEq_append_singleton_of_remove hRemove⟩

/-- `SemEq` defines an equivalence relation on rows. -/
theorem semEq_isEquivalence : Equivalence SemEq where
  refl := semEq_refl
  symm := semEq_symm
  trans := semEq_trans

instance : Setoid Row where
  r := SemEq
  iseqv := semEq_isEquivalence

/-- Canonical setoid instance for row semantic equivalence. -/
def rowSetoid : Setoid Row := inferInstance

/--
Quotient row semantics where rows are identified by semantic equivalence (`≈`).

This is a canonical semantic boundary without requiring a concrete normalized
syntactic representation.
-/
abbrev RowSet := Quotient rowSetoid

/-- Inject a syntactic row into the semantic row quotient. -/
def toRowSet (row : Row) : RowSet :=
  Quotient.mk rowSetoid row

/-- Append on semantic rows, well-defined modulo `≈`. -/
def appendRowSet (lhs rhs : RowSet) : RowSet :=
  Quotient.liftOn₂ lhs rhs
    (fun lhs rhs => Quotient.mk _ (lhs ++ rhs))
    (by
      intro lhs rhs lhs' rhs' hL hR
      exact Quotient.sound (semEq_trans (semEq_append_congr_left hL) (semEq_append_congr_right hR)))

instance : Append RowSet where
  append := appendRowSet

/-- Singleton semantic row. -/
def singletonRowSet (effect : Type) : RowSet :=
  toRowSet (singleton effect)

/--
Canonical semantic discharge equality induced by a one-step removal witness.
-/
theorem toRowSet_remove_discharge {effect : Type} {src out : Row} :
    Remove effect src out → toRowSet src = singletonRowSet effect ++ toRowSet out := by
  intro hRemove
  have hDecomp : SemEq src (out ++ singleton effect) := semEq_append_singleton_of_remove hRemove
  have hComm : toRowSet (out ++ singleton effect) = toRowSet (singleton effect ++ out) := by
    exact Quotient.sound (semEq_append_comm out (singleton effect))
  calc
    toRowSet src = toRowSet (out ++ singleton effect) := Quotient.sound hDecomp
    _ = toRowSet (singleton effect ++ out) := hComm
    _ = singletonRowSet effect ++ toRowSet out := by rfl

/-- Append is commutative in the semantic row quotient. -/
theorem appendRowSet_comm (lhs rhs : RowSet) : lhs ++ rhs = rhs ++ lhs := by
  refine Quotient.inductionOn₂ lhs rhs ?_
  intro a b
  exact Quotient.sound (semEq_append_comm a b)

/-- Append is idempotent in the semantic row quotient. -/
theorem appendRowSet_idem (row : RowSet) : row ++ row = row := by
  refine Quotient.inductionOn row ?_
  intro a
  exact Quotient.sound (semEq_append_idem a)

/-- Append is associative in the semantic row quotient. -/
theorem appendRowSet_assoc (a b c : RowSet) : (a ++ b) ++ c = a ++ (b ++ c) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro a' b' c'
  exact Quotient.sound (semEq_append_assoc a' b' c')

end Row
end Kernel
end Klean
