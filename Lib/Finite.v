Require Export Category.Lib.List.

Generalizable All Variables.
Set Universe Polymorphism.

Import ListNotations.

Definition CoverAll `{Setoid A} (l : list A) := ∀ x, In x l.

Class Finite `(S : Setoid A) :=
  { cover : list A
  ; cover_all : CoverAll cover
  }.

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

Lemma reduce_cover
  `{FIN : @Finite A SET} {EqDec : Decidable SET} (l : list A) (COVER : CoverAll l)
  : CoverAll (reduce l COVER).
Proof.
  (* TODO *)
Admitted.

Definition cardinality `(FIN : @Finite A SET) {EqDec : Decidable SET} : nat :=
  length (reduce cover cover_all).