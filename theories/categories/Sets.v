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

  Program Definition BinaryProduct : t × t ⟶ t :=
    {|
      fobj := λ XY, from_type (_set XY.1 * _set XY.2);
      fmap := λ _ _ fg xy, (fg.1 xy.1, fg.2 xy.2);
    |}.
  Next Obligation. apply func_ext=> [] [x y] //. Qed.
End Sets.
Existing Instance Sets.t.
Coercion Sets._set : Sets.Object >-> Sortclass.
Coercion Sets.from_type : Sortclass >-> Sets.Object.

Lemma Sets_id_unfold X x : id{Sets.t}[X]%morphism x = x.
Proof. rewrite /cat_id //. Qed.
Lemma Sets_comp_unfold [X Y Z : Sets.Object] (f : Y ~> Z) (g : X ~> Y) x : (f ∘ g)%morphism x = f (g x).
Proof. rewrite /comp //. Qed.
#[export] Hint Rewrite @Sets_id_unfold @Sets_comp_unfold : normalize.

Program Definition Powerset : Sets.t ⟶ Sets.t :=
  {|
    fobj := λ X, X → Prop;
    fmap := λ X Y f P y, ∃ x, P x ∧ y = f x;
  |}.
Next Obligation.
  apply func_ext. i. apply pred_ext. i.
  cby split=> [[?] [/[swap] ->]|].
Qed.
Next Obligation.
  apply func_ext. i. apply pred_ext. i.
  cby split=> [[?] [/[swap] ->]|[?] [[?] /[swap] ->] [/[swap] ->]].
Qed.

Module SetsNotations.
  Declare Scope sets_scope.
  Delimit Scope sets_scope with sets.
  Bind Scope sets_scope with Sets.Object.

  Notation "X × Y" := (Sets.from_type (Sets._set X%sets * Sets._set Y%sets)%type) : sets_scope.
  Notation "X + Y" := (Sets.from_type (Sets._set X%sets + Sets._set Y%sets)%type) : sets_scope.
  Notation "X → Y" := (Sets.from_type (Sets._set X%sets → Sets._set Y%sets)%type) : sets_scope.
  Notation "'𝒫'" := Powerset (at level 0) : sets_scope.
  Notation "'(-×-)'" := Sets.BinaryProduct (at level 0) : sets_scope.
End SetsNotations.