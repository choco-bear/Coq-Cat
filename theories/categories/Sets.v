Require Import Common.

#[local] Instance set_arrow_equiv (X Y : Type) : Equiv (X → Y) := eq.
#[local] Instance set_arrow_equivalence (X Y : Type) : Equivalence (≡@{X → Y}) := _.

Program Instance Sets : Category Type :=
  {|
    Arrow := λ X Y, X → Y;
    comp := @compose;
    cat_id := λ X x, x;
  |}.

Lemma Sets_id_unfold X x : id{Sets}[X]%morphism x = x.
Proof. rewrite /cat_id //. Qed.
#[export] Hint Rewrite @Sets_id_unfold : normalize.