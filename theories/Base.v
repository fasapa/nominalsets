Global Generalizable All Variables.
From Coq Require Export
     Classes.Morphisms
     Relations.Relations
     (* Classes.SetoidTactics *)
     Program.Program
     Lists.List
     Bool
     Unicode.Utf8.
Export ListNotations.

Declare Scope nominal_scope.
Delimit Scope nominal_scope with nominal.
Global Open Scope nominal.

Infix "≡" := eq (at level 70, no associativity): nominal_scope.
Notation "(≡)" := eq (only parsing): nominal_scope.
Notation "( x ≡)" := (eq x) (only parsing): nominal_scope.
Notation "(≡ x )" := (λ y, eq y x) (only parsing): nominal_scope.
Notation "(≢)" := (λ x y, ¬x ≡ y) (only parsing): nominal_scope.
Notation "x ≢ y":= (¬x ≡ y) (at level 70, no associativity): nominal_scope.
Notation "( x ≢)" := (λ y, x ≢ y) (only parsing): nominal_scope.
Notation "(≢ x )" := (λ y, y ≢ x) (only parsing): nominal_scope.
