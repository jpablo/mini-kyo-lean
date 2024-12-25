
/-
Attempt to translate the following Scala code to Lean:
https://gist.github.com/fwbrasil/8c8b2b0236793391546c624cbbacd421
("minified version of Kyo's kernel")

TODO:

1. Model contravariance.

In Scala, given a type like `trait <[+A, -S]`
the compiler can prove that (B < S₂) <:< (B < (S & S₂))

2. Replace the usage of .asInstanceOf in handleState:
val (newState, v) = f(s.input.asInstanceOf, state, s.cont.asInstanceOf)

3. Add more effects

-/

-- Using Coercions to model subtyping

infixl:65 " <: " => CoeOut

def impossible {T : Empty -> Type _} (e) : T e :=
  Empty.elim e

/-! Using `Empty` as bottom and `Unit` as top  -/
instance :     A <: A    := ⟨id⟩
instance : Coe Empty A   := ⟨impossible⟩
instance :     A <: Unit := ⟨fun _ => ()⟩


structure Intersection (A B : Type) where
  value : A × B

infixl:65 " & " => Intersection

----------------------

class Tag (E : Type) where
  tag : String

/-
Using a type class instead of subtypes for ArrowEffects.
For example:
  sealed trait Abort[V] extends ArrowEffect[Const[V], Const[Nothing]]
is modeled as
  instance {V : Type} : ArrowEffect (E := Abort V) (I := Const V) (O := Const Empty) where
-/
class ArrowEffect (E: Type) (I : Type -> Type) (O : Type -> Type) where

-- Lean simplification: use Type and Type 1 instead of universe polymorphism
inductive Eff : Type -> Type -> Type 1 where
  -- simplification: Use Eff A S instead of Eff A Unit
  | Pure {A S} (value : A) : Eff A S

  | Suspend {I O : Type -> Type} {E} [ae: ArrowEffect E I O] {A B S}
      (tag : Tag E)
      (input : I A)
      (cont : O A -> Eff B S) :
      Eff B S

def Const (A : Type) : Type → Type := fun _ => A

namespace Eff
  infixl:65 " < " => Eff

  -- simplification: Use A < S instead of A < Unit
  def pure {A S} (x : A) : A < S :=
    Pure x

  def suspend {I O: Type -> Type} {E} [ae : ArrowEffect E I O] {A} (tag : Tag E) (input : I A) : (O A) < E  :=
    Suspend (ae := ae) (B := O A) (S := E) tag input pure

  def continue_ {A B S} (x : A < S) (f : A < S -> B < S) : B < S :=
    match x with
    | p@ (Pure _) => f p
    | Suspend tag input cont =>
      Suspend tag input (fun o => f (cont o))


  def flatMap {A B S S₂} (x : A < S) (f : A -> B < S₂) : B < (S & S₂) :=
    match x with
    -- Problem: need to convert B < S₂ to B < (S & S₂)
    | Pure a => f a
    | (Suspend tag input cont) =>
      Suspend tag input (fun o => (cont o).flatMap f)

  def map {A B S} (x : A < S) (f : A -> B) : B < S :=
    -- Problem: need to convert B < (S & _) to B < S
    x.flatMap (fun a => pure (f a))

  def handleState {I O : Type -> Type} {E} [ae : ArrowEffect E I O] {State A S: Type}
      (tag : Tag E)
      (state: State)
      (v0 : A < (E & S))
      (f : {C : Type} -> I C -> State -> (O C -> A < (E & S)) -> (State × A < (E & S))
    ) : (State × A) < S :=
    let rec loop (state: State) (v : A < (E & S)) : (State × A) < S :=
      match h:v with
      | Pure value =>
        Pure (state, value)

      | v@(@Suspend I' O' _ ae' x _ _ tag' input cont) =>
        if tag.tag == tag'.tag then
          -- Problem: need to prove that I' x = I x
          let (newState, v1) := f input state cont
          loop newState v1
        else
          -- Problem: need to convert A < (E & S) to A < (E & (E & S))
          v.continue_ (fun a => handleState tag state a f)
    loop state v0


  def handle {I O : Type -> Type} {E} [ae: ArrowEffect E I O] {A S}
      (tag : Tag E)
      (v : A < E)
      (f : {C : Type} -> I C -> (O C -> A < S) -> A < S
    ) : A < S :=
      -- Problem: need to A < E convert A < (E & _)
      let s := handleState (O := O) tag () v (fun {_: Type} input _ cont => ((), f input cont))
      s.map (fun x => x.snd)

    def eval {A S} [Inhabited A] (v : A < S) : A :=
      match v with
      | Pure x => x
      | _ => panic! "eval: not a Pure"

end Eff


--------------
-- Abort
--------------
inductive Abort (V : Type) where


inductive Result (E A : Type) where
  | Success (value : A) :  Result E A
  | Fail (error : E) :  Result E A
deriving Repr

namespace Abort

  instance {V : Type} : ArrowEffect (E := Abort V) (I := Const V) (O := Const Empty) where

  instance {V} [tagV: Tag V] : Tag (Abort V) where
    tag := s!"Abort({tagV.tag})"

  def fail {V : Type} [Tag V] (value : V) : Empty < (Abort V) :=
    Eff.suspend (I := Const V) (O := Const Empty) (A := Empty) inferInstance value

  def run {V : Type} [Tag V] {A S : Type} (v : A < (Abort V /- & S -/)) : (Result V A) < S :=
    Eff.handle
      (I := Const V)
      (O := Const Empty)
      (E := Abort V)
      (tag := inferInstance)
      (v := v.map (fun r => Result.Success r))
      (f := fun {_ : Type} input _ => Eff.pure (Result.Fail input))
end Abort


--------------
-- Env --
--------------

inductive Env (V : Type) where


namespace Env

  instance {V : Type}: ArrowEffect (E := Env V) (I := Const Unit) (O := Const V) where

  instance {V} [tagV: Tag V] : Tag (Env V) where
    tag := s!"Env({tagV.tag})"

  def get {V : Type} [Tag V] : V < (Env V) :=
    Eff.suspend (I := Const Unit) (O := Const V) (A := V) (tag := inferInstance) (input := ())

  def run {V : Type} [Tag V] {A S: Type} (value : V) (v : A < (Env V)) : A < S :=
    Eff.handle
      (I := Const Unit)
      (O := Const V)
      (tag := inferInstance)
      (v := v)
      (f := fun _ cont => cont value)

end Env

--------------
-- Var --
--------------

inductive Var (V : Type) where

namespace Var

  inductive Op (V₀ : Type) where
    | Get
    | Set (v : V₀)

  instance varAE {V : Type}: ArrowEffect
    (E := Var V)
    (I := Const (Op V))
    (O := Id) where

  instance {V : Type} : Tag (Var V) where
    tag := "Var"

  def get {V : Type} [Tag V] : V < (Var V) :=
    Eff.suspend (I := Const (Op V)) (O := Id) (A := V) inferInstance Op.Get

  def set {V : Type} [Tag V] (value : V) : Unit < (Var V) :=
    Eff.suspend (I := Const (Op V)) (O := Id) (A := Unit) inferInstance (Op.Set value)

  def run {V : Type} [Tag V] {A S : Type} (state : V) (v : A < ((Var V) & S)) : (V × A) < S :=
    Eff.handleState
      (I := Const (Op V))
      (O := Id)
      (E := Var V)
      (ae := varAE)
      (State := V)
      (A := A)
      (S := S)
      (tag := inferInstance)
      (state := state)
      (v0 := v)
      (f := fun {C} input (state : V) cont =>
        match input with
        -- Problem: Need to prove that V can be used as C
        | Op.Get => (state, cont state)
        | Op.Set newState => (newState, cont ())
      )

end Var
