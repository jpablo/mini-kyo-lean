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

end Row
end Kernel
end Klean
