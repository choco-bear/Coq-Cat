Require Import CommonTactics CommonFacts Category.

Create HintDb assoc_left discriminated.
Global Hint Rewrite <- @comp_assoc : assoc_left.

Create HintDb assoc_right discriminated.
Global Hint Rewrite @comp_assoc : assoc_right.

Lemma left_comp `{C : Category Obj} [x y z : Obj] (f g : x ~> y) (h : y ~> z)
  : f = g → h ∘ f =[C] h ∘ g.
Proof. by intros ->. Qed.

Lemma right_comp `{C : Category Obj} [x y z : Obj] (f g : y ~> z) (h : x ~> y)
  : f = g → f ∘ h =[C] g ∘ h.
Proof. by intros ->. Qed.

Tactic Notation "left_comp" uconstr(p) :=
  autorewrite with assoc_left; unshelve simple refine (left_comp _ _ p _); autorewrite with assoc_right.

Tactic Notation "left_comp" uconstr(p) "in" hyp(H) :=
  match type of H with
  | @eq ?A ?f ?g => eapply (left_comp f g p) in H; autorewrite with assoc_right in H
  | @eq ?A ?f ?g => fail 1 "The hypothesis" H "is not an equality between morphisms"
  | _ => fail 1 "The hypothesis" H "is not an equality"
  end.
  
Tactic Notation "left_comp" uconstr(p) "in" hyp(H) "as" ident(name) :=
  match type of H with
  | @eq ?A ?f ?g => eapply (left_comp f g p) in H as name; autorewrite with assoc_right in name
  | @eq ?A ?f ?g => fail 1 "The hypothesis" H "is not an equality between morphisms"
  | _ => fail 1 "The hypothesis" H "is not an equality"
  end.

Tactic Notation "right_comp" uconstr(p) :=
  autorewrite with assoc_right; unshelve simple refine (right_comp _ _ p _); autorewrite with assoc_right.

Tactic Notation "right_comp" uconstr(p) "in" hyp(H) :=
  match type of H with
  | @eq ?A ?f ?g => eapply (right_comp f g p) in H; autorewrite with assoc_right in H
  | @eq ?A ?f ?g => fail 1 "The hypothesis" H "is not an equality between morphisms"
  | _ => fail 1 "The hypothesis" H "is not an equality"
  end.

Tactic Notation "right_comp" uconstr(p) "in" hyp(H) "as" ident(name) :=
  match type of H with
  | @eq ?A ?f ?g => eapply (right_comp f g p) in H as name; autorewrite with assoc_right in name
  | @eq ?A ?f ?g => fail 1 "The hypothesis" H "is not an equality between morphisms"
  | _ => fail 1 "The hypothesis" H "is not an equality"
  end.