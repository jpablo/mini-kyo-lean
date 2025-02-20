
/-
Translation of the following Scala code to Lean:
https://gist.github.com/fwbrasil/7a4c8af789db6b1f0c07a6243616883f
("mini-unsafe.scala")

TODO:

1. Address non-termination
2. Replace the usage of .asInstanceOf in handle:
3. Correct signature of IO

-/


namespace kernel

  /-
  Using a type class instead of subtypes for ArrowEffects.
  For example:
    sealed trait Abort[V] extends ArrowEffect[V, Nothing]
  is modeled as
    instance {V} : ArrowEffect (Abort V) v Empty where
  -/

  class ArrowEffect (E I O : Type) where

  class Tag (E : Type) where
    tag : String 

  instance : Tag Unit := ⟨"Unit"⟩
  instance : Tag Int := ⟨"Int"⟩
  instance : Tag Nat := ⟨"Nat"⟩

  inductive Kyo : Type -> Type 1 where
    | Pure (value : A) : Kyo A

    | Suspend {E} [ArrowEffect E I O]
        (tag : Tag E)
        (input : I)
        (cont : O -> Kyo A)
        : Kyo A
  deriving Nonempty


  def Const (A : Type) : Type → Type := fun _ => A

  namespace Kyo
    def pure {A} (value : A) : Kyo A :=
      Pure value

    def suspend {I O E} [ArrowEffect E I O] (tag : Tag E) (input : I) : Kyo O :=
      Suspend tag input pure

    def continue_ {A B} (x : Kyo A) (f : Kyo A -> Kyo B) : Kyo B :=
      match x with
      | p@ (Pure _) => f p
      | Suspend tag input cont =>
        Suspend tag input (fun o => f (cont o))

    def flatMap {A B} (x : Kyo A) (f : A -> Kyo B) : Kyo B :=
      match x with
      | Pure a => f a
      | Suspend tag input cont =>
        Suspend tag input (fun o => flatMap (cont o) f)

    def map {A B} (x : Kyo A) (f : A -> B) : Kyo B :=
      x.flatMap (fun a => pure (f a))

    partial def handle {I O E A} [ArrowEffect E I O] (tag : Tag E) (v : Kyo A)
        (f : I -> (O -> Kyo A) -> Kyo A) : Kyo A :=
      match v with
      | Pure value => Pure value
      | @Suspend I' O' _ _  _ tag' input cont =>
        -- Problem input has type I✝ but expected type I (likewise for O)
        if tag.tag == tag'.tag then
          let ii: I' = I := by sorry
          let oo: O = O' := by sorry
          let input' := cast ii input
          let cont' := cont ∘ cast oo
          handle tag (f input' cont') f
        else
          Suspend tag' input (fun o => handle tag (cont o) f)

    def eval {A} [Inhabited A] (v : Kyo A) : A :=
      match v with
      | Pure x => x
      | _ => panic! "eval: not a Pure"

  end Kyo

end kernel

open kernel
open kernel.Kyo


--------------
-- Abort
--------------

inductive Abort (V : Type) where

inductive Result (E A : Type) where
  | Success (value : A)
  | Fail (error : E)
deriving Repr

namespace Abort

  instance {V} : ArrowEffect (Abort V) v Empty where

  instance {V} [tagV: Tag V] : Tag (Abort V) where
    tag := s!"Abort({tagV.tag})"

  def fail {V} [Tag V] (value : V) : Kyo Empty :=
    suspend (E := Abort V) (tag := inferInstance) value

  def run {V A} [Tag V] (v : Kyo A) : Kyo (Result V A) :=
    handle (O := Empty) (E := Abort V)
      inferInstance
      (v.map Result.Success)
      (fun input _ => pure (Result.Fail input))

end Abort


--------------
-- Env --
--------------

inductive Env (V : Type) where

namespace Env

  instance {V}: ArrowEffect (Env V) I V where

  instance {V} [tagV: Tag V] : Tag (Env V) where
    tag := s!"Env({tagV.tag})"

  def get {V} [Tag V] : Kyo V :=
    suspend (E := Env V) inferInstance ()

  def run {V} [Tag V] {A} (value : V) (v : Kyo A) : Kyo A :=
    handle (I := Unit) (E := Env V) inferInstance v (fun _ cont => cont value)

end Env


--------------
-- Var --
--------------

inductive Var (V : Type) where

namespace Var

  inductive Op (V : Type) where
  | Get
  | Set (v : V)

  instance {V}: ArrowEffect (Var V) (Op V) V where

  instance {V}  [tagV: Tag V]: Tag (Var V) where
    tag := s!"Var({tagV.tag})"

  def get (V) [Tag V] : Kyo V :=
    suspend (I := Op V) (E := Var V) inferInstance Op.Get

  def set {V} [Tag V] (value : V) : Kyo Unit :=
    suspend (O := V) (E := Var V) inferInstance (Op.Set value)
      |>.map (fun _ => ())


  def run {V A} [Tag V] (state : V) (v : Kyo A) [Tag (Var V)] : Kyo (V × A) :=
    -- Problem: fail to show termination for Var.run.loop
    let rec loop (state : V) (v : Kyo (V × A)) : Kyo (V × A) := sorry
      -- handle
      --   (E := Var V)
      --   (tag := inferInstance) v
      --   (fun input cont =>
      --     match input with
      --     | Op.Get => cont state
      --     | Op.Set newState => loop newState (cont newState))
    loop state (v.map (fun a => (state, a)))


end Var


--------------
-- Emit --
--------------

inductive Emit (V : Type) where

namespace Emit

  instance ae {V}: ArrowEffect (Emit V) V Unit where

  instance {V}  [tagV: Tag V] : Tag (Emit V) where
    tag := s!"Emit({tagV.tag})"

  def apply {V} [Tag V] (value : V) : Kyo Unit :=
    suspend (tag := inferInstanceAs (Tag (Emit V))) value


  def run {V A} [Tag V] (v : Kyo A) : Kyo (Array V × A) :=
    -- Problem: fail to show termination for Emit.run.loop
    let rec loop (acc : Array V) (v : Kyo (Array V × A)) : Kyo (Array V × A) :=
      sorry
      -- handle (tag := inferInstanceAs (Tag (Emit V))) v
      --   (fun input cont =>
      --     loop (acc.push input) (cont ()))
    loop #[] (v.map (fun a => (#[], a)))

end Emit


--------------
-- IO --
--------------

namespace kIO

  instance {V}: ArrowEffect (IO V) Unit Unit where

  instance {V} [tagV : Tag V] : Tag (IO V) where
    tag := s!"IO({tagV.tag})"

  def unit : Kyo Unit :=
    suspend (tag := inferInstanceAs (Tag (IO Unit))) ()

  -- TODO: this should have signature
  -- def apply {A} [Tag A] (v : IO A) : Kyo A
  def apply {A} [Tag A] (v : IO A) : Kyo (IO A) :=
    unit.map (fun _ => v)

  -- def run {A} [tagIO: Tag A] (v: Kyo (IO A)) : Kyo (IO A) :=
  --   Kyo.handle
  --     (A := A)
  --     (tag := inferInstanceAs (Tag (IO A)))
  --     v
  --     (fun _ cont => cont ())

end kIO


--- Examples ---

partial def cumulativeSum (acc : Int) : Kyo Int :=
  (Var.get Int).flatMap <| fun
    | 0 => pure acc
    | n => (Var.set (n - 1)).flatMap (fun _ => cumulativeSum (acc + n))


def ex1 :=
  eval (Var.run 10 (cumulativeSum 0))

-- #eval r1
