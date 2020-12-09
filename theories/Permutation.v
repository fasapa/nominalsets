From Nom Require Export Atom Group Swap.

(** *Permutation *)
Declare Scope perm_scope.
Delimit Scope perm_scope with perm.

Notation Perm := (list (Atom * Atom)).
(* Definition Perm := list (Atom * Atom). *)

Definition perm_act_atom (p: Perm) c: Atom :=
  fold_left (fun w q => swap (fst q) (snd q) w) p c.

Section PermEquiv.
  Definition perm_equiv (p q: Perm): Prop :=
    forall x, perm_act_atom p x ≡ perm_act_atom q x.
  Local Hint Unfold perm_equiv: core.

  Global Program Instance PermEquivRefl: Reflexive perm_equiv.
  Global Program Instance PermEquivSymm: Symmetric perm_equiv.
  Global Program Instance PermEquivTrans: Transitive perm_equiv.
  Next Obligation. unfold perm_equiv in *; intros; eapply eq_trans; eauto. Qed.
  Global Instance PermEquiv: Equiv Perm. exact perm_equiv. Defined.
  Global Program Instance PermSetoid: Setoid Perm.
  Next Obligation. split; typeclasses eauto. Qed.
End PermEquiv.
Arguments PermEquiv p q/.
Arguments perm_equiv /.

Section PermActProperties.
  Lemma perm_act_atom_concat (p: Perm): forall q x,
    perm_act_atom (p ++ q) x ≡ perm_act_atom q (perm_act_atom p x).
  Proof with (auto). induction p; intros; simpl... Qed.

  Lemma perm_act_atom_rev_left1 (p: Perm):
    forall x, perm_act_atom p (perm_act_atom (rev p) x) ≡ x.
  Proof with (auto).
    induction p; intros; simpl...
    rewrite perm_act_atom_concat; simpl; rewrite swap_involutive...
  Qed.

  Lemma perm_act_atom_rev_left (p: Perm) x:
    perm_act_atom (rev p ++ p) x ≡ x.
  Proof. rewrite perm_act_atom_concat; apply perm_act_atom_rev_left1. Qed.

  Lemma perm_act_atom_rev_right1 (p: Perm):
    forall x, perm_act_atom (rev p) (perm_act_atom p x) ≡ x.
  Proof with auto.
    induction p; intros; simpl...
    rewrite perm_act_atom_concat; simpl; rewrite IHp;
      apply swap_involutive.
  Qed.

  Lemma perm_act_atom_rev_right (p: Perm) x:
    perm_act_atom (p ++ rev p) x ≡ x.
  Proof. rewrite perm_act_atom_concat; apply perm_act_atom_rev_right1. Qed.

  Lemma perm_act_atom_rev_equiv (p q: Perm):
    p = q -> (rev p) = (rev q).
  Proof with auto.
    intros H x; transitivity (perm_act_atom (rev q ++ p ++ rev p) x);
      repeat rewrite perm_act_atom_concat.
    - rewrite H, perm_act_atom_rev_left1...
    - rewrite perm_act_atom_rev_right1...
  Qed.
End PermActProperties.

(** *Perm additive group  *)
Require Import Properties.

Instance perm_unit: Neutral Perm. exact (@nil (Atom * Atom)). Defined.
Instance perm_op: Binop Perm. exact (@app (Atom * Atom)). Defined.
Instance perm_inv: Negate Perm. exact (@rev (Atom * Atom)). Defined.
Arguments perm_unit /.
Arguments perm_op /.
Arguments perm_inv /.

Program Instance: Associative perm_op.
Next Obligation. rewrite app_assoc; auto. Qed.
Program Instance: RightIdentity perm_op perm_unit.
Next Obligation. rewrite app_nil_r; auto. Qed.
Program Instance: LeftInverse perm_op perm_inv perm_unit.
Next Obligation. unfold equiv; simpl; intros; rewrite perm_act_atom_rev_left; auto. Qed.
Program Instance: RightInverse perm_op perm_inv perm_unit.
Next Obligation. unfold equiv; simpl; intros; rewrite perm_act_atom_rev_right; auto. Qed.
Program Instance: LeftIdentity perm_op perm_unit.

Program Instance PermGroup: @Group Perm PermEquiv perm_unit perm_inv perm_op :=
  { g_setoid := PermSetoid }.
Next Obligation. (* perm_op preserve perm_equiv *)
  intros ? ? HE1 ? ? HE2; unfold equiv,"+" in *; simpl in *; intros;
    repeat rewrite perm_act_atom_concat; rewrite HE1,HE2; reflexivity.
Qed.
Next Obligation. (* perm_neg preserve perm_equiv *)
  intros ? ? HE; unfold negate,equiv in *; simpl in *; intros;
    apply perm_act_atom_rev_equiv; auto.
Qed.
