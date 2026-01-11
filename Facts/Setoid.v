Require Import Category.Lib.
Require Import Category.Axioms.
From Category.Theory Require Import
  Category
  Morphisms
  Isomorphism
  Terminal
  Initial
  Functor.
Require Import Category.Construction.Opposite.
From Category.Instance Require Import Sets Fin.

Generalizable All Variables.

Definition Idempotent_Split `(IDEM : @Idempotent Sets X f) : Split f.
Proof.
  construct; [exact {X & λ x, x ≡ f x}|..].
    { (* epimorphism *)
      construct.
      + now exists (f X0); rewrite <-idempotent at 1.
      + now proper; rewrites.
    }
    all: by try construct.
Qed.

Program Definition from_nonempty_is_regular `{Choice}
  `(f : X ~{Sets}~> Y) (x : X) : Regular f :=
  {| pseudo_inverse := _ |}.
Next Obligation.
  set ((λ x y, f x ≡ f y) : crelation X) as R.
  assert (EQUIV : Equivalence R) by by unfold R; construct.
  unshelve esplit.
  - intro y. classic (∃ x, f x ≡ y) as HIm.
    + clear x. destruct HIm as [x EQ].
      destruct (AC_fun_repr EQUIV) as [CHOICE HCHOICE].
      exact (CHOICE x).
    + exact x.
  - ss. classic.
    {
      destruct (AC_fun_repr EQUIV) as [C RW].
      destruct (RW x1) as [_ RW'].
      erewrite RW'; try reflexivity.
      now red; rewrite e, e0.
    } all: now exfalso; apply n; eexists; rewrites.
Defined.
Next Obligation.
  classic; [|now exfalso; apply n; eexists].
  remember (AC_fun_repr _) as s; destruct s as [CHOICE HCHOICE]; clear Heqs.
  now destruct (HCHOICE x0) as [<- _].
Defined.

Program Instance Sets_Terminal : @Terminal Sets :=
  {| terminal_obj := unit_setoid : Sets |}.
Next Obligation. construct; intuition. Defined.
Next Obligation. now destruct (f a), (g a). Qed.

Program Instance Sets_Initial : @Initial Sets :=
  {| terminal_obj := void_setoid : Sets |}.
Next Obligation. construct; intuition. Defined.
Next Obligation. intuition. Qed.

Section Powerset.
  #[local] Obligation Tactic := proper; ss; rewrites; try done.
  Program Definition Powerset : Sets^op ⟶ Sets :=
    {|  fobj := λ X, property_setoid X
      ; fmap := λ Y X f, {| morphism := λ P, (λ x, `1 P (f x); _) |}
    |}.
  Next Obligation. now property; rewrites. Defined.
  Next Obligation.
    - now rewrite <-X0; eauto.
    - now rewrite X0; eauto.
  Defined.
End Powerset.
Notation 𝒫 := Powerset.

Section Isomorphism.
End Isomorphism.

Section Finite.
  #[export]
  Program Instance isomorphism_preserves_cardinality `{ExcludedMiddle}
    : Proper (Isomorphism ==> eq) (λ X : Fin, cardinality X).
  Next Obligation.
    (* TODO *)
  Admitted.
End Finite.