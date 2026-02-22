Require Import CommonTactics CommonFacts Category.

Lemma left_comp `{C : Category Obj} [x y z : Obj] (f g : x ~> y) (h : y ~> z)
  : f = g → h ∘ f =[C] h ∘ g.
Proof. by intros ->. Qed.

Lemma right_comp `{C : Category Obj} [x y z : Obj] (f g : y ~> z) (h : x ~> y)
  : f = g → f ∘ h =[C] g ∘ h.
Proof. by intros ->. Qed.

Tactic Notation "left_comp" uconstr(p) :=
  rewrite -?comp_assoc; unshelve simple refine (left_comp _ _ p _); rewrite ?comp_assoc.

Tactic Notation "left_comp" uconstr(p) "in" hyp(H) :=
  match type of H with
  | @eq ?A ?f ?g => eapply (left_comp f g p) in H; rewrite ?comp_assoc in H
  | @eq ?A ?f ?g => fail 1 "The hypothesis" H "is not an equality between morphisms"
  | _ => fail 1 "The hypothesis" H "is not an equality"
  end.
  
Tactic Notation "left_comp" uconstr(p) "in" hyp(H) "as" ident(name) :=
  match type of H with
  | @eq ?A ?f ?g => eapply (left_comp f g p) in H as name; rewrite ?comp_assoc in name
  | @eq ?A ?f ?g => fail 1 "The hypothesis" H "is not an equality between morphisms"
  | _ => fail 1 "The hypothesis" H "is not an equality"
  end.

Tactic Notation "right_comp" uconstr(p) :=
  rewrite ?comp_assoc; unshelve simple refine (right_comp _ _ p _); rewrite ?comp_assoc.

Tactic Notation "right_comp" uconstr(p) "in" hyp(H) :=
  match type of H with
  | @eq ?A ?f ?g => eapply (right_comp f g p) in H; rewrite ?comp_assoc in H
  | @eq ?A ?f ?g => fail 1 "The hypothesis" H "is not an equality between morphisms"
  | _ => fail 1 "The hypothesis" H "is not an equality"
  end.

Tactic Notation "right_comp" uconstr(p) "in" hyp(H) "as" ident(name) :=
  match type of H with
  | @eq ?A ?f ?g => eapply (right_comp f g p) in H as name; rewrite ?comp_assoc in name
  | @eq ?A ?f ?g => fail 1 "The hypothesis" H "is not an equality between morphisms"
  | _ => fail 1 "The hypothesis" H "is not an equality"
  end.