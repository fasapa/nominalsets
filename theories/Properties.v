Global Generalizable All Variables.
From Nom Require Import Base Equiv.

Class Idempotent `{Ea: Equiv A} (f: A → A → A) (x: A) : Prop :=
  idempotency: f x x = x.
Arguments idempotency {A Ea} _ _ {Idempotent}.

Class Involutive `{Equiv A} (f : A → A) := involutive: ∀ x, f (f x) = x.

Class LeftIdentity {A} `{Equiv B} (op : A → B → B) (x : A): Prop :=
  left_identity: ∀ y, op x y = y.
Class RightIdentity `{Equiv A} {B} (op : A → B → A) (y : B): Prop :=
  right_identity: ∀ x, op x y = x.

Class LeftInverse {A} {B} `{Equiv C} (op : A → B → C) (inv : B → A) (unit : C)
  := left_inverse: ∀ x, op (inv x) x = unit.
Class RightInverse {A} {B} `{Equiv C} (op : A → B → C) (inv : A → B) (unit : C)
  := right_inverse: ∀ x, op x (inv x) = unit.

Class Commutative `{Equiv B} `(f : A → A → B) : Prop :=
  commutativity: ∀ x y, f x y = f y x.
Class Associative `{Equiv A} f: Prop :=
  associativity: forall x y z, f x (f y z) = f (f x y) z.

Class Injective `{Equiv A} `{Equiv B} (f: A -> B) : Prop :=
    { injective : ∀ x y, f x = f y → x = y
    ; injective_proper :> Proper ((=) ==> (=)) f }.
