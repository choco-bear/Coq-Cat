Require Import CommonTactics CommonFacts Category.
Require Import Functor FunctorTactics FunctorFacts.
Require Import NatTrans.

Lemma nat_trans_ext `{C : Category ObjC} `{D : Category ObjD} {F G : C ⟶ D} (τ μ : F ⟹ G)
  : (∀ x, τ x =[D] μ x) → τ = μ.
Proof.
  rewrite /component. depdes τ μ. i. apply func_ext_dep in H as <-.
  by assert (naturality = naturality0) as <- by apply proof_irr.
Qed.