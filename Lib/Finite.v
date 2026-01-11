Require Import Coq.Lists.List.

Require Export Category.Lib.List.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Import ListNotations.

Definition CoverAll `{Setoid A} (l : list A) := ∀ x, In x l.

Class Finite `(S : Setoid A) :=
  { cover : list A
  ; cover_all : CoverAll cover
  }.

Definition FinType X := @Finite X (eq_Setoid X).

Fixpoint Fin_cover n : list (Fin.t n) :=
  match n as n0 return list (Fin.t n0) with
  | O => []
  | S n' => Fin.F1 :: map Fin.FS (Fin_cover n')
  end.

Lemma Fin_cover_correct n : CoverAll (Fin_cover n).
Proof.
  induction n as [| n IHn].
  - intros x. inversion x.
  - ii. revert n x IHn.
    apply (Fin.caseS (λ n y, CoverAll (Fin_cover n) → In y (Fin_cover (S n)))).
    + ss. now econs.
    + ss. apply In_skip. apply In_map; eauto.
      proper. now inversion H0; subst.
Qed.

Definition Finite_Fin_Setoid n : Finite (@Fin_Setoid n) :=
  {|  cover := Fin_cover n
    ; cover_all := Fin_cover_correct n
  |}.

Fixpoint _reduce_aux
  `{FIN : @Finite A SET} {EqDec : Decidable SET} (acc l : list A) (COVER : CoverAll (acc ++ l))
  : list A :=
    match l as l0 return (CoverAll (acc ++ l0) → list A) with
    | [] => λ _, acc
    | x :: l' => λ COVER,
        match In_Dec x l' with
        | inl IN => 
            _reduce_aux acc l' (
              λ y, In_or_app y acc l' (
                match In_app_or y acc (x :: l') (COVER y) with
                | inl H => inl H
                | inr H =>
                    match dec_equiv x y with
                    | inl e =>
                        inr (In_respects_helper x y e l' l' (Equivalence_Reflexive l') IN)
                    | inr n => 
                        match In_cons_or y x l' H with
                        | inl e => match n e with end
                        | inr H => inr H
                        end
                    end
                end))
        | inr NIN =>
            _reduce_aux
              (acc ++ [x])
              l'
              (eq_rect
                (acc ++ x :: l')
                CoverAll
                COVER
                ((acc ++ [x]) ++ l')
                (app_assoc acc [x] l'))
        end
    end COVER.

Definition reduce `{FIN : @Finite A SET} {EqDec : Decidable SET} (l : list A) (COVER : CoverAll l)
  : list A := _reduce_aux [] l COVER.

Lemma reduce_aux_cover
  `{FIN : @Finite A SET} {EqDec : Decidable SET}
  (l : list A) (acc : list A) (COVER : CoverAll (acc ++ l))
  : CoverAll (_reduce_aux acc l COVER).
Proof.
  revert acc COVER.
  induction l; i.
  - now s; rewrite app_nil_r in COVER.
  - s. destruct (In_Dec a l); apply IHl.
Qed.

Lemma reduce_cover
  `{FIN : @Finite A SET} {EqDec : Decidable SET} (l : list A) (COVER : CoverAll l)
  : CoverAll (reduce l COVER).
Proof. unfold reduce. apply reduce_aux_cover. Qed.

Definition cardinality `(FIN : @Finite A SET) {EqDec : Decidable SET} : nat :=
  length (reduce cover cover_all).