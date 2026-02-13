Require Import Program Axioms sflib Category.
From stdpp Require Import ssreflect.

Lemma cat_ext_JMeq `(C : Category Obj) `(C' : Category Obj')
  : Obj = Obj'
  → JMeq hom[C] hom[C']
  → JMeq (@Arrow_equiv _ C) (@Arrow_equiv _ C')
  → JMeq (@comp _ C) (@comp _ C')
  → JMeq (@cat_id _ C) (@cat_id _ C')
  → JMeq C C'.
Proof.
  rewrite /Category.comp /Category.cat_id.
  intros <- eqHom eqEquiv eqComp eqId. depdes C C'. ss.
  apply JMeq_eq in eqHom as <-.
  apply JMeq_eq in eqComp as <-.
  apply JMeq_eq in eqEquiv as <-.
  apply JMeq_eq in eqId as <-.
  replace Arrow_equivalence0 with Arrow_equivalence by apply proof_irr.
  replace comp_proper0 with comp_proper by apply proof_irr.
  replace comp_assoc0 with comp_assoc by apply proof_irr.
  replace cat_id_left0 with cat_id_left by apply proof_irr.
  by replace cat_id_right0 with cat_id_right by apply proof_irr.
Qed.

Lemma cat_ext [Obj : Type] (C C' : Category Obj)
  : JMeq hom[C] hom[C']
  → JMeq (@Arrow_equiv _ C) (@Arrow_equiv _ C')
  → JMeq (@comp _ C) (@comp _ C')
  → JMeq (@cat_id _ C) (@cat_id _ C')
  → C = C'.
Proof. by i; apply JMeq_eq, cat_ext_JMeq. Qed.

Global Instance opposite_involutive [Obj : Type] : Involutive eq (ᵒᵖ)@{Obj}.
Proof. by ii; apply cat_ext. Qed.