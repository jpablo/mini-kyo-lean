/-!
Kernel acceptance validations for the first effect trio:
- `Abort`
- `Env`
- `Var`

This module is intentionally self-contained. It validates the intended handler
semantics with small fuel-bounded interpreters while the generic suspend layer
is still under active design.
-/

namespace Klean
namespace Kernel
namespace Validation

namespace Abort

inductive Result (Error A : Type) where
  | ok (value : A) : Result Error A
  | err (error : Error) : Result Error A
deriving Repr, DecidableEq

inductive Prog (Error A : Type) where
  | pure (value : A) : Prog Error A
  | fail (error : Error) : Prog Error A
  | defer (thunk : Unit → Prog Error A) : Prog Error A

def flatMap (self : Prog Error A) (f : A → Prog Error B) : Prog Error B :=
  match self with
  | .pure value => f value
  | .fail error => .fail error
  | .defer thunk => .defer (fun _ => flatMap (thunk ()) f)

def run : Nat → Prog Error A → Option (Result Error A)
  | 0, _ => none
  | Nat.succ _, .pure value => some (.ok value)
  | Nat.succ _, .fail error => some (.err error)
  | Nat.succ fuel, .defer thunk => run fuel (thunk ())

def abortEval : Option (Result String Nat) :=
  run 8 (.fail "boom")

theorem abortEval_spec : abortEval = some (.err "boom") := rfl

end Abort

namespace Env

inductive Prog (Value A : Type) where
  | pure (value : A) : Prog Value A
  | get (cont : Value → Prog Value A) : Prog Value A
  | defer (thunk : Unit → Prog Value A) : Prog Value A

def flatMap (self : Prog Value A) (f : A → Prog Value B) : Prog Value B :=
  match self with
  | .pure value => f value
  | .get cont => .get (fun env => flatMap (cont env) f)
  | .defer thunk => .defer (fun _ => flatMap (thunk ()) f)

def run (env : Value) : Nat → Prog Value A → Option A
  | 0, _ => none
  | Nat.succ _, .pure value => some value
  | Nat.succ fuel, .get cont => run env fuel (cont env)
  | Nat.succ fuel, .defer thunk => run env fuel (thunk ())

def envEval : Option Nat :=
  run 42 8 (.get .pure)

theorem envEval_spec : envEval = some 42 := rfl

end Env

namespace Var

inductive Prog (Value A : Type) where
  | pure (value : A) : Prog Value A
  | get (cont : Value → Prog Value A) : Prog Value A
  | set (value : Value) (cont : Unit → Prog Value A) : Prog Value A
  | defer (thunk : Unit → Prog Value A) : Prog Value A

def flatMap (self : Prog Value A) (f : A → Prog Value B) : Prog Value B :=
  match self with
  | .pure value => f value
  | .get cont => .get (fun state => flatMap (cont state) f)
  | .set value cont => .set value (fun _ => flatMap (cont ()) f)
  | .defer thunk => .defer (fun _ => flatMap (thunk ()) f)

def run (state : Value) : Nat → Prog Value A → Option (Value × A)
  | 0, _ => none
  | Nat.succ _, .pure value => some (state, value)
  | Nat.succ fuel, .get cont => run state fuel (cont state)
  | Nat.succ fuel, .set newState cont => run newState fuel (cont ())
  | Nat.succ fuel, .defer thunk => run state fuel (thunk ())

def program : Prog Nat Nat :=
  flatMap (.get .pure) (fun n =>
    flatMap (.set (n + 1) (fun _ => .pure ())) (fun _ =>
      .pure (n * 2)))

def varEval : Option (Nat × Nat) :=
  run 10 16 program

theorem varEval_spec : varEval = some (11, 20) := rfl

end Var

end Validation
end Kernel
end Klean
