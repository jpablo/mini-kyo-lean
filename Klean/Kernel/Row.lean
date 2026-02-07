/-!
A first effect-row representation for Klean.

This is intentionally simple: a row is an ordered spine of effect types.
Normalization and canonical equivalence are planned in later iterations.
-/

namespace Klean
namespace Kernel

inductive Row where
  | empty : Row
  | cons (effect : Type) (tail : Row) : Row

infixr:67 " ::ᵣ " => Row.cons

namespace Row

def append : Row → Row → Row
  | .empty, rhs => rhs
  | .cons eff tl, rhs => .cons eff (append tl rhs)

instance : Append Row where
  append := append

def singleton (effect : Type) : Row :=
  .cons effect .empty

inductive Contains (effect : Type) : Row → Prop where
  | here {tail} : Contains effect (.cons effect tail)
  | there {head tail} : Contains effect tail → Contains effect (.cons head tail)

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
