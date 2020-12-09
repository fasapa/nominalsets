From Nom Require Import Equiv.
From Coq Require Import Arith Arith.PeanoNat MSets.

(** *Nomes Atômicos *)
(** Átomos são identificadores, sua estrutura é irrelevante (opaca). As únicas propriedades de
    interesse que nomes devem possuir são:
    - Sempre podemos obter um átomo novo dado um conjunto de átomos (infinito).
    - Distinguíveis, ou seja, a igualdade entre átomos é decidível.

    Implementamos átomos como módulos de interface opaca (estrutura irrelevante). A igualdade
    é definida como a igualdade padrão (usual) do Coq decidível: igualdade de Leibniz.
    "Leibniz equality is a relation and every function
    is a morphism that respects Leibniz equality."
    https://coq.inria.fr/refman/addendum/generalized-rewriting.html
    Check eq_rect. *)

Module Type ATOM <: UsualDecidableType.

  Parameter t: Set.

  Parameter eq_dec : forall x y: t, {x ≡ y} + {x ≢ y}.

  Parameter fresh_from_list: forall (xs : list t), {x : t | ~ List.In x xs}.

  Parameter fresh: list t -> t.

  Parameter fresh_notin_list : forall l, ~ In (fresh l) l.

  (* HasUsualEq: iguladade de Leibniz (usual) para átomos.
     UsualIsEq: iguladade entre átomos é uma relação de equivalência. *)
  Include HasUsualEq <+ UsualIsEq.
End ATOM.

Module Atom: ATOM.

  Definition t := nat.
  Definition eq_dec := eq_nat_dec.

  Lemma nat_list_max :
    forall xs : list nat, { n : nat | forall x, List.In x xs -> x <= n }.
  Proof.
    induction xs as [| x ? [y IH]].
    - exists 0. inversion 1.
    - exists (max x y); intros ? []; subst;
          [apply Nat.le_max_l | apply Nat.max_le_iff; right; apply IH]; auto.
  Qed.

  Lemma fresh_from_list : forall xs, {x: t | ~ List.In x xs}.
  Proof.
    intros xs; destruct (nat_list_max xs) as [x H].
    exists (S x); intros F; apply H in F; apply Nat.nle_succ_diag_l in F; auto.
  Qed.

  Definition fresh l := proj1_sig (fresh_from_list l).

  Lemma fresh_notin_list: forall l, ~ In (fresh l) l.
  Proof.
    intros; unfold fresh; destruct (fresh_from_list _);
      simpl in *; auto.
  Qed.

  Include HasUsualEq <+ UsualIsEq.
End Atom.
Infix "≡a" := Atom.eq_dec (at level 70, no associativity): nominal_scope.
