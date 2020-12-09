Require Import Equiv Properties.

(* Como teremos apenas um grupo podemos definir a classe Group bundled.
   Para a classe ActionGroup e NominalSets seria interessante fazer
   unbundled.

   Exemplo de unbundled:
   Group {A} {Setoid A} (null: A) (op: A -> A -> A) (inv: A -> A) := {
      assoc: forall p1 p2 p3, op p1 (op p2 p3) == op (op p1 p2) p3;
      left_inv: forall p, op p (inv p) == null
   }.

   Uma vantagem do unblundled é que podemos definir multiplas instâncias
   diferentes de grupos para um mesmo tipo através de diferentes operações
   e operadores. No bundled teremos problema de overlaping instances.

   O problema deste método é que não temos como referenciar as operações,
   e operadores: null, op e inv. Para isso é necessário definir
   cada um como uma classe unitária:
   Class GroupOp A := grp_op: A -> A -> A.

   Exemplo bundled:
   Group (A: Type) := {
      grp_setoid :> Setoid A;
      null: A;
      grp_op: A -> A -> A;
      grp_inv: A -> A;

      assoc: forall p1 p2 p3, op p1 (op p2 p3) == op (op p1 p2) p3;
      left_inv: forall p, op p (inv p) == null
   }. *)

(** *Canonical names  *)
Class Neutral A := neutral: A.
Class Binop A := b_op: A -> A -> A.
Class Negate A := negate: A -> A.
Typeclasses Transparent Neutral Binop Negate.

Infix "+" := b_op (at level 50, left associativity) : nominal_scope.
Notation "(+)" := b_op (only parsing) : nominal_scope.
Notation "( x +)" := (b_op x) (only parsing) : nominal_scope.
Notation "(+ x )" := (λ y, y + x) (only parsing) : nominal_scope.

Notation "- x" := (negate x) : nominal_scope.
Notation "(-)" := negate (only parsing) : nominal_scope.
Notation "x - y" := (x + -y)%nominal : nominal_scope.

Section GroupClass.
  Context A {Ea: Equiv A}.

  Class Group {GU: Neutral A} {GN: Negate A} {GOp: Binop A}: Prop :=
    { g_setoid :> Setoid A;
      g_op_proper :> Proper ((=) ==> (=) ==> (=)) (+);
      g_ne_proper :> Proper ((=) ==> (=)) (-);
      g_assoc :> Associative (+);
      g_left_id :> LeftIdentity (+) neutral;
      g_right_id :> RightIdentity (+) neutral;
      g_left_inv :> LeftInverse (+) (-) neutral;
      g_right_inv :> RightInverse (+) (-) neutral
    }.
End GroupClass.
Arguments g_op_proper {_ _ _ _ _ _}.
Arguments g_ne_proper {_ _ _ _ _ _}.
Arguments g_right_inv {_ _ _ _ _ _}.
Arguments g_left_inv {_ _ _ _ _ _}.

Section GroupProperties.
  Context `{Group G}.

  Global Instance negate_involutive: Involutive (-).
  Proof.
    intros x; rewrite <-(left_identity x) at 2;
      rewrite <- (left_inverse (-x)), <- associativity,
      left_inverse, right_identity.
    reflexivity.
  Qed.

  Global Instance: Injective (-).
  Proof.
    repeat (split; try apply _);
      intros x y E; rewrite <-(involutive x), <-(involutive y), E;
        reflexivity.
  Qed.

  Lemma negate_neutral: -neutral = neutral.
  Proof.
    rewrite <-(left_inverse neutral) at 2; rewrite right_identity;
      reflexivity.
  Qed.
End GroupProperties.

(** *Group Action *)
Class Action `(Group A) X := action: A -> X -> X.
Infix "∙" := action (at level 50, left associativity): nominal_scope.
Notation "(∙)" := action (only parsing).
Typeclasses Transparent Action.

Section GroupAction.
  (* Action of Group A over set X *)
  Context `(Ga: Group A) X {Ex: Equiv X}.

  (* Left group action *)
  Class GroupAction {GAct: Action Ga X}: Prop :=
    { gct_setoid :> Setoid X;
      gct_proper :> Proper ((=) ==> (=) ==> (=)) (∙);
      gct_compat: forall p q r, p ∙ (q ∙ r) = (q + p) ∙ r;
      gct_id :> LeftIdentity (∙) neutral }.
End GroupAction.
Arguments gct_proper {_ _ _ _ _ _ _ _ _ _}.
Arguments gct_compat {_ _ _ _ _ _ _ _ _ _}.
Arguments gct_id {_ _ _ _ _ _ _ _ _ _}.
