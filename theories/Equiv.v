Require Export Base.

(* Unbundle Equivalence and setoid *)
Class Equiv A := equiv: relation A.
Typeclasses Transparent Equiv.

Infix "=" := equiv : type_scope.
Notation "(=)" := equiv (only parsing) : nominal_scope.
Notation "( x =)" := (equiv x) (only parsing) : nominal_scope.
Notation "(= x )" := (λ y, equiv y x) (only parsing) : nominal_scope.
Notation "(≠)" := (λ x y, ¬x = y) (only parsing) : nominal_scope.
Notation "x ≠ y":= (¬x = y): type_scope.
Notation "( x ≠)" := (λ y, x ≠ y) (only parsing) : nominal_scope.
Notation "(≠ x )" := (λ y, y ≠ x) (only parsing) : nominal_scope.

Ltac auto_symm :=
  match goal with
    [ H: ?R ?x ?y |- ?R ?y ?x] => apply (symmetry H)
  end.
Ltac auto_trans :=
  match goal with
    [ H: ?R ?x ?y, I: ?R ?y ?z |- ?R ?x ?z] => apply (transitivity H I)
  end.
Hint Extern 2 (?x = ?x) => reflexivity: core.
Hint Extern 2 (?x = ?y) => auto_symm: core.
Hint Extern 2 (?x = ?y) => auto_trans: core.

Definition ext_equiv `{Equiv A} `{Equiv B} : Equiv (A → B) := ((=) ==> (=))%signature.
Hint Extern 10 (Equiv (_ → _)) => apply @ext_equiv : typeclass_instances.
Hint Extern 10 (Equiv (relation _)) => apply @ext_equiv : typeclass_instances.

(* (* Coq sometimes uses an incorrect DefaultRelation, so we override it. *) *)
(* Instance equiv_default_relation `{Equiv A} : DefaultRelation (=) | 3 := {}. *)

Class Setoid A {Ae : Equiv A} : Prop := setoid_eq :> Equivalence (@equiv A Ae).
