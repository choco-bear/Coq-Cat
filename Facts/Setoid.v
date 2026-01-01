Require Import Category.Lib.
Require Import Category.Axioms.Excluded_Middle.
From Category.Theory Require Import
  Category
  Morphisms.
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

Definition from_nonempty_is_regular `{ExcludedMiddle}
  `(f : X ~{Sets}~> Y) (x : X) : Regular f.
Proof.
  construct.
  {
    unshelve esplit.
    - intro y. classic (∃ x, f x ≡ y) as HIm.
      + destruct HIm as [x' EQ]. exact x'.
      + exact x.
    - proper. admit.
  }
Admitted.