
/-
  Some ideas on how to encode subtyping and intersection types in Lean.
-/

infixl:65 " <: " => CoeOut

def impossible {T : Empty -> Type _} (e) : T e :=
  Empty.elim e

/-! Using `Empty` as bottom and `Unit` as top  -/

instance :     A <: A    := ⟨id⟩
instance : Coe Empty A   := ⟨impossible⟩
instance :     A <: Unit := ⟨fun _ => ()⟩


-- https://docs.scala-lang.org/scala3/reference/new-types/intersection-types-spec.html

structure Intersection (A B : Type) where
  value : A × B

infixl:65 " & " => Intersection

def simplify_to (E S: Type) : (E & S) → (E & (E & S)) :=
  fun x => ⟨(x.value.1, ⟨x.value.1, x.value.2⟩)⟩

def simplify_from (E S: Type) : (E & (E & S)) → (E & S) :=
  fun x => ⟨(x.value.1, x.value.2.value.2)⟩



instance {A B T : Type} [T <: A] [T <: B] : T <: (A & B) where
  coe x := ⟨(x, x)⟩

instance {A B T : Type} [A <: T] : (A & B) <: T where
  coe x := x.value.1

instance {A B T : Type} [B <: T] : (A & B) <: T where
  coe x := x.value.2


instance {A B : Type} : (A & B) <: A where
  coe x := x.value.1

instance {A B : Type} : (A & B) <: B where
  coe x := x.value.2
