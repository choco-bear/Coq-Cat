Require Import Common.

Module Sets.
  Structure Object := from_type { _set : Type }.

  Local Notation SetsArrow := (λ X Y : Object, _set X → _set Y).
  
  Program Instance t : Category Object :=
    {|
      Arrow := SetsArrow;
      comp := λ X Y Z f g, (f ∘ g)%stdpp;
      cat_id := λ X x, x;
    |}.
End Sets.
Existing Instance Sets.t.
Coercion Sets._set : Sets.Object >-> Sortclass.
Coercion Sets.from_type : Sortclass >-> Sets.Object.

Declare Scope sets_scope.
Delimit Scope sets_scope with sets.
Bind Scope sets_scope with Sets.Object.

Notation "X × Y" := (Sets.from_type (Sets._set X%sets * Sets._set Y%sets)%type) : sets_scope.
Notation "X + Y" := (Sets.from_type (Sets._set X%sets + Sets._set Y%sets)%type) : sets_scope.
Notation "'2^' X" := (Sets.from_type (Sets._set X%sets → Prop)%type) (at level 8, right associativity, format "2^ X") : sets_scope.
Notation "X → Y" := (Sets.from_type (Sets._set X%sets → Sets._set Y%sets)%type) : sets_scope.

Local Open Scope sets_scope.

Lemma Sets_id_unfold X x : id{Sets.t}[X]%morphism x = x.
Proof. rewrite /cat_id //. Qed.
Lemma Sets_comp_unfold [X Y Z : Sets.Object] (f : Y ~> Z) (g : X ~> Y) x : (f ∘ g)%morphism x = f (g x).
Proof. rewrite /comp //. Qed.
#[export] Hint Rewrite @Sets_id_unfold @Sets_comp_unfold : normalize.

Program Definition Powerset : Sets.t ⟶ Sets.t :=
  {|
    fobj := λ X, 2^X;
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