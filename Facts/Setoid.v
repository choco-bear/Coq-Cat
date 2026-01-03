Require Import Category.Lib.
Require Import Category.Axioms.
From Category.Theory Require Import
  Category
  Morphisms
  Terminal.
Require Import Category.Instance.Sets.

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

Program Instance initial_void : Initial (void_setoid : Sets).
Next Obligation. construct; intuition. Defined.
Next Obligation. intuition. Qed.

Program Instance terminal_unit : Terminal (unit_setoid : Sets).
Next Obligation. construct; intuition. Defined.
Next Obligation. now destruct (f a), (g a). Qed.