Require Export Program Axioms sflib.
Require Export Permutation Orders String HexString ZArith List.
Export ListNotations.

From stdpp Require Export ssreflect.

Declare Scope coqcat_scope.
Delimit Scope coqcat_scope with coqcat.
#[export] Open Scope coqcat_scope.

Create HintDb normalize discriminated.
Create HintDb coqcat discriminated.

Global Hint Rewrite @compose_id_right @compose_id_left : normalize.

Ltac common_normalize := autorewrite with normalize.
Tactic Notation "common_normalize" "in" hyp(H) := autorewrite with normalize in H.
Tactic Notation "common_normalize" "in" "*" "|-" := repeat_on_hyps (fun H => common_normalize in H).
Tactic Notation "common_normalize" "in" "*" := autorewrite with normalize in *.

Inductive Void : Type := .

Global Instance Void_pi : ProofIrrel Void := λ x, match x with end.

Class Unique (A : Type) := {
  #[export] unique_inhabited :: Inhabited A;
  #[export] unique_proof_irrel :: ProofIrrel A;
}.

Notation "●" := (@inhabitant _ unique_inhabited) : coqcat_scope.

Ltac address_pi :=
  match goal with
  | [|- @eq ?A _ _] =>
      tryif (
        assert (ProofIrrel A) by apply _
      ) then (
        apply proof_irrel
      ) else idtac
  | _ => idtac
  end.

Ltac address_inhabited :=
  match goal with
  | [|- ?A] =>
      tryif (
        assert (Inhabited A) by apply _
      ) then (
        apply inhabitant
      ) else idtac
  end.

Lemma unique_collapse [A B : Type] (f : A → B) (x : A) `{!Unique B} : f x = ●.
Proof. apply proof_irrel. Qed.

Ltac simpl_unique :=
  hrepeat do 1 match goal with
  | [x : ?A |- _] =>
      let A_is_unique := fresh A "_is_unique" in
      progress tryif (
        assert (A_is_unique : Unique A) by apply _
      ) then (
        depdes x; clear A_is_unique
      ) else idtac
  end; hrepeat do 1 progress rewrite @unique_collapse in *.

Ltac common_simpl_prep := ii; ss; subst; try apply _; try solve_proper; simpl_unique.

Ltac common_simpl :=
  common_simpl_prep;
  tryif (
    solve [ common_normalize in *; try by address_pi; try by address_inhabited; eauto with coqcat]
  ) then idtac else (
    common_normalize; try by address_pi; try by address_inhabited; eauto with coqcat
  ).

Tactic Notation "cby" tactic(t) := t; common_simpl; done.

Hint Extern 10 (_ * _) => split : coqcat.

Global Obligation Tactic := program_simpl; common_simpl.

Global Program Instance unit_unique : Unique ().
Global Program Instance true_unique : Unique True.

Lemma fapply [A B : Type] (f : A → B) [x y : A] : x = y → f x = f y.
Proof. i; rewrite H //. Qed.

Tactic Notation "fapply" uconstr(f) "in" hyp(H) := eapply (fapply f) in H.
Tactic Notation "fapply" uconstr(f) "in" hyp(H) "as" ident(name) := eapply (fapply f) in H as name. 

Lemma duplicate_goal P : P → P → P.
Proof. ss. Qed.

Ltac duplicate_goal := match goal with [|- ?G ] => apply (duplicate_goal G) end.

Ltac construct := unshelve econstructor; ii; ss.

Notation CReflexive := CRelationClasses.Reflexive.
Notation CSymmetric := CRelationClasses.Symmetric.
Notation CTransitive := CRelationClasses.Transitive.
Notation CEquivalence := CRelationClasses.Equivalence.
Notation CEquivalence_CReflexive := CRelationClasses.Equivalence_Reflexive.
Notation CEquivalence_CSymmetric := CRelationClasses.Equivalence_Symmetric.
Notation CEquivalence_CTransitive := CRelationClasses.Equivalence_Transitive.
Notation CAntisymmetric := CRelationClasses.Antisymmetric.
Notation CAsymmetric := CRelationClasses.Asymmetric.
Notation CPreOrder := CRelationClasses.PreOrder.
Notation CPreOrder_CReflexive := CRelationClasses.PreOrder_Reflexive.
Notation CPreOrder_CTransitive := CRelationClasses.PreOrder_Transitive.
Notation CPartialOrder := CRelationClasses.PartialOrder.
Notation crelation := CRelationClasses.crelation.