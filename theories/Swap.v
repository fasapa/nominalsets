Require Import Atom.

Definition swap (a b: Atom): Atom -> Atom :=
  fun c => if a ≡a c then b else (if b ≡a c then a else c).

Lemma swap_id a b: swap a a b ≡ b.
Proof. unfold swap; repeat destruct (_ ≡a _); auto. Qed.

Lemma swap_left a b: swap a b a ≡ b.
Proof. unfold swap; repeat destruct (_ ≡a _); auto; congruence. Qed.

Lemma swap_right a b: swap b a a ≡ b.
Proof. unfold swap; repeat destruct (_ ≡a _); auto; congruence. Qed.

Lemma swap_involutive a b c: swap a b (swap a b c) ≡ c.
Proof.
  intros; unfold swap; repeat destruct (_ ≡a _); intuition.
  do 2 match goal with | H: _ ≡ _ |- _ => rewrite <- H end; auto.
Qed.

Lemma swap_neither a b c: a ≢ c -> b ≢ c -> swap a b c ≡ c.
Proof. intros; unfold swap; repeat destruct (_ ≡a _); auto; congruence. Qed.

Lemma swap_switch a b c: swap a b c ≡ swap b a c.
Proof.
  unfold swap; repeat destruct (_ ≡a _); auto;
    repeat match goal with | H: _ ≡ _ |- _ => rewrite H end; auto.
Qed.

(* Program Instance swap_injective a b: Injective (swap a b). *)
(* Next Obligation. unfold swap in *; repeat destruct (_ ≡≡ _); congruence. Qed. *)

(* Program Instance swap_surjective (a b: atom): Surjective (swap a b). *)
(* Next Obligation. exists (swap a b y); apply swap_involutive. Qed. *)
