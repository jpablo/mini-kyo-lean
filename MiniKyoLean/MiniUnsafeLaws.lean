import MiniKyoLean.MiniUnsafe


/-

  * Left Identity
  *   - pure(a).flatMap(f) ≡ f(a)
  *
  * Right Identity
  *   - m.flatMap(pure) ≡ m
  *
  * Associativity
  *   - m.flatMap(f).flatMap(g) ≡ m.flatMap(x => f(x).flatMap(g))
  *
  * Pure Handling
  *   - handle(tag, pure(value), f) ≡ pure(value)
  *
  * Effect Handling
  *   - handle(tag1, suspend(tag2, input, cont), f) ≡ handle(tag1, f(input, cont), f) where tag1 ≡ tag2
  *
  * Handler Rotation
  *   - handle(tag1, suspend(tag2, input, cont), f) ≡ suspend(tag2, input, x => handle(tag1, cont(x), f)) where tag1 ≠ tag2


 -/

open kernel
open kernel.Kyo

theorem leftIdentity {A B : Type} (a : A) (f : A -> Kyo B) : ((pure a).flatMap f) = f a :=
  rfl

theorem rightIdentity {A : Type} (m : Kyo A) : m.flatMap pure = m :=
  match m with
  | Kyo.Pure a => rfl
  | Suspend tag input cont =>
    by
      -- unfold flatMap
      simp [flatMap]
      funext o
      exact rightIdentity (cont o)

theorem associativity
  {A B C : Type} (m : Kyo A) (f : A -> Kyo B) (g : B -> Kyo C)
  : (m.flatMap f).flatMap g = m.flatMap (fun x => (f x).flatMap g) :=
  match m with
  | Kyo.Pure a => rfl
  | Suspend tag input cont =>
    by
      simp [flatMap]
      funext o
      exact associativity (cont o) f g
