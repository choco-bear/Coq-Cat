Require Import Common.

Program Instance Sets : Category Type :=
  {|
    Arrow := λ X Y, X → Y;
    comp := @compose;
    cat_id := λ X x, x;
  |}.

Lemma Sets_id_unfold X x : id{Sets}[X]%morphism x = x.
Proof. rewrite /cat_id //. Qed.
Lemma Sets_comp_unfold [X Y Z : Type] (f : Y ~> Z) (g : X ~> Y) x : (f ∘ g)%morphism x = f (g x).
Proof. rewrite /comp //. Qed.
#[export] Hint Rewrite @Sets_id_unfold @Sets_comp_unfold : normalize.

Program Definition Powerset : Sets ⟶ Sets :=
  {|
    fobj := λ X, X → Prop;
    fmap := λ X Y f P y, ∃ x, P x ∧ y = f x;
  |}.
Next Obligation.
  rename x into X.
  apply func_ext=> P. common_normalize. apply pred_ext=> x.
  split=> [[y] [/[swap] ->]|]; common_normalize; eauto.
Qed.
Next Obligation.
  rename x into X. rename y into Y. rename z into Z.
  apply func_ext=> P. common_normalize. apply pred_ext=> z.
  split=> [[x] [/[swap] ->]|[y] [[x] /[swap] ->] [/[swap] ->]]; common_normalize; eauto.
Qed.