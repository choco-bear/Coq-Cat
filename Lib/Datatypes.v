Require Import Coq.Lists.List.

Require Export Category.Lib.Arith.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Import ListNotations.

Local Set Warnings "-intuition-auto-with-star".

(** The only inductive types from the standard library used in this development
  * are products and sums, so we must show how they interact with constructive
  * setoids.
  *)

#[global]
Program Instance prod_setoid {A B} `{Setoid A} `{Setoid B}
  : Setoid (A * B) :=
    { equiv := fun x y => (fst x ≡ fst y) * (snd x ≡ snd y) }.

Lemma prod_setoid_equiv_simpl {A B} `{Setoid A} `{Setoid B} (a a' : A) (b b' : B)
  : ((a, b) ≡ (a', b')) = ((a ≡ a') ∧ (b ≡ b')).
Proof. unfold prod_setoid, equiv; ss. Qed.
#[global] Hint Rewrite @prod_setoid_equiv_simpl : core categories.

#[global]
Program Instance pair_respects {A B} `{Setoid A} `{Setoid B}
  : Proper (equiv ==> equiv ==> equiv) (@pair A B).

#[global]
Program Instance fst_respects {A B} `{Setoid A} `{Setoid B}
  : Proper (equiv ==> equiv) (@fst A B).

#[global]
Program Instance snd_respects {A B} `{Setoid A} `{Setoid B}
  : Proper (equiv ==> equiv) (@snd A B).

Definition fst_simpl {A B} (a : A) (b : B) : fst (a,b) = a := eq_refl.
Definition snd_simpl {A B} (a : A) (b : B) : snd (a,b) = b := eq_refl.
#[global] Hint Rewrite @fst_simpl @snd_simpl : core normalize categories.

Corollary let_fst {x y} (A : x * y) `(f : x → z)
  : (let (x, _) := A in f x) = f (fst A).
Proof. destruct A; auto. Qed.

Corollary let_snd {x y} (A : x * y) `(f : y → z)
  : (let (_, y) := A in f y) = f (snd A).
Proof. destruct A; auto. Qed.

Corollary let_projT1 {A P} (S : @sigT A P) `(f : A → z)
  : (let (x, _) := S in f x) = f (projT1 S).
Proof. destruct S; auto. Qed.

Corollary let_projT2 {A P} (S : @sigT A P) `(f : ∀ x, P x → z)
  : (let (x, y) := S in f x y) = f (projT1 S) (projT2 S).
Proof. destruct S; auto. Qed.

#[global]
Program Instance sum_setoid {A B} `{Setoid A} `{Setoid B}
  : Setoid (A + B) :=
    { equiv := fun x y => match x with
                          | inl x =>
                              match y with
                              | inl y => equiv x y
                              | inr y => poly_void
                              end
                          | inr x =>
                              match y with
                              | inl y => poly_void
                              | inr y => equiv x y
                              end
                          end
    }.
Next Obligation.
  equivalence; destruct x, y; try destruct z; intuition; auto with *.
Qed.

#[global]
Program Instance inl_respects {A B} `{Setoid A} `{Setoid B}
  : Proper (equiv ==> equiv) (@inl A B).

#[global]
Program Instance inr_respects {A B} `{Setoid A} `{Setoid B}
  : Proper (equiv ==> equiv) (@inr A B).

#[global]
Program Instance option_setoid `{Setoid A} : Setoid (option A) :=
  { equiv := fun x y => match x, y with
                        | Some x, Some y => x ≡ y
                        | None, None => poly_unit
                        | _, _ => poly_void
                        end
  }.
Next Obligation.
  equivalence.
  - destruct x; reflexivity.
  - destruct x, y; auto.
    symmetry; auto.
  - destruct x, y, z; auto.
      transitivity a0; auto.
    contradiction.
Qed.

#[global]
Program Instance Some_respects {A} `{Setoid A} : Proper (equiv ==> equiv) (@Some A).

(** TODO : Define [Decidable] and [remove] without using [Prop] universe, and
  *        comment out the below. *)
(* Lemma length_remove A (A_eq_dec : ∀ x y : A, { x = y } + { x <> y }) x xs
  : (length (remove A_eq_dec x xs) <= length xs)%nat.
Proof.
  induction xs; auto.
  simpl.
  destruct (A_eq_dec x a); subst.
    apply PeanoNat.Nat.le_le_succ_r, IHxs.
  simpl.
  apply le_n_S, IHxs.
Qed. *)

(** TODO : Define symmetric product without using [Prop] universe. *)
(* Section Symmetric_Product2.
  Variable A : Type.
  Variable leA : A → A → Prop.

  Inductive symprod2 : A * A → A * A → Prop :=
    | left_sym2 :
        ∀ x x':A, leA x x' → ∀ y:A, symprod2 (x, y) (x', y)
    | right_sym2 :
        ∀ y y':A, leA y y' → ∀ x:A, symprod2 (x, y) (x, y')
    | both_sym2 :
        ∀ (x x':A) (y y':A),
          leA x x' →
          leA y y' →
          symprod2 (x, y) (x', y').

  Lemma Acc_symprod2 : ∀ x:A, Acc leA x → ∀ y:A, Acc leA y → Acc symprod2 (x, y).
  Proof.
    induction 1 as [x _ IHAcc]; intros y H2.
    induction H2 as [x1 H3 IHAcc1].
    apply Acc_intro; intros y H5.
    inversion_clear H5; auto with sets.
    apply IHAcc; auto.
    apply Acc_intro; trivial.
  Defined.

  Lemma wf_symprod2 : well_founded leA → well_founded symprod2.
  Proof.
    red.
    destruct a.
    apply Acc_symprod2; auto with sets.
  Defined.
End Symmetric_Product2. *)