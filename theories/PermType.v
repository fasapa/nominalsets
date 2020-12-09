From Nom Require Import Permutation Properties.

(** *Permutation Sets  *)
Class PermAction X := perm_action :> Action PermGroup X.
Class PermType `{Ex: Equiv X} (PAct: PermAction X): Prop :=
  pset_gct :> GroupAction PermGroup X.
Arguments perm_action _ _ _/.

Section PermTypeProperties.
  Context `{PermType X}.

  Lemma permt_left_inv (x: X) p: (-p) ∙ (p ∙ x) = x.
  Proof. rewrite gct_compat, g_right_inv, gct_id; auto. Qed.

  Lemma permt_right_inv (x: X) p: p ∙ (-p ∙ x) = x.
  Proof. rewrite gct_compat, g_left_inv, gct_id; auto. Qed.

  Lemma permt_iff (x y: X) p: p ∙ x = y <-> x = (-p) ∙ y.
  Proof.
    split; intros A; [rewrite <-A; symmetry | rewrite ->A ].
    - apply permt_left_inv.
    - apply permt_right_inv.
  Qed.

  Global Instance permset_injective p: Injective (action p).
  Proof with (try typeclasses eauto).
    split... intros ? y HH; rewrite <-(permt_left_inv y p);
        apply permt_iff in HH; auto.
  Qed.
End PermTypeProperties.
