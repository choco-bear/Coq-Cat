Require Import CommonTactics CommonFacts Category.

Create HintDb assoc_left discriminated.
Global Hint Rewrite @comp_assoc : assoc_left.

Create HintDb assoc_right discriminated.
Global Hint Rewrite <- @comp_assoc : assoc_right.

Lemma left_comp `{C : Category Obj} [x y z : Obj] (f g : x ~> y) (h : y ~> z)
  : f = g → h ∘ f =[C] h ∘ g.
Proof. by intros ->. Qed.

Lemma right_comp `{C : Category Obj} [x y z : Obj] (f g : y ~> z) (h : x ~> y)
  : f = g → f ∘ h =[C] g ∘ h.
Proof. by intros ->. Qed.

Tactic Notation "cancel_l" uconstr(p) :=
  autorewrite with assoc_right; unshelve simple refine (left_comp _ _ p _); autorewrite with assoc_left.
Tactic Notation "cancel_l" := cancel_l _.

Tactic Notation "comp_l" uconstr(p) "in" hyp(H) :=
  match type of H with
  | @eq ?A ?f ?g => eapply (left_comp f g p) in H; autorewrite with assoc_left in H
  | @eq ?A ?f ?g => fail 1 "The hypothesis" H "is not an equality between morphisms, or the term" p "is not appropriate"
  | _ => fail 1 "The hypothesis" H "is not an equality"
  end.
  
Tactic Notation "comp_l" uconstr(p) "in" hyp(H) "as" ident(name) :=
  match type of H with
  | @eq ?A ?f ?g => eapply (left_comp f g p) in H as name; autorewrite with assoc_left in name
  | @eq ?A ?f ?g => fail 1 "The hypothesis" H "is not an equality between morphisms, or the term" p "is not appropriate"
  | _ => fail 1 "The hypothesis" H "is not an equality"
  end.

Tactic Notation "cancel_r" uconstr(p) :=
  autorewrite with assoc_left; unshelve simple refine (right_comp _ _ p _); autorewrite with assoc_left.
Tactic Notation "cancel_r" := cancel_r _.

Tactic Notation "comp_r" uconstr(p) "in" hyp(H) :=
  match type of H with
  | @eq ?A ?f ?g => eapply (right_comp f g p) in H; autorewrite with assoc_left in H
  | @eq ?A ?f ?g => fail 1 "The hypothesis" H "is not an equality between morphisms, or the term" p "is not appropriate"
  | _ => fail 1 "The hypothesis" H "is not an equality"
  end.

Tactic Notation "comp_r" uconstr(p) "in" hyp(H) "as" ident(name) :=
  match type of H with
  | @eq ?A ?f ?g => eapply (right_comp f g p) in H as name; autorewrite with assoc_left in name
  | @eq ?A ?f ?g => fail 1 "The hypothesis" H "is not an equality between morphisms, or the term" p "is not appropriate"
  | _ => fail 1 "The hypothesis" H "is not an equality"
  end.

Ltac deal_discrete := repeat match goal with
                      | f : ?x ~{?C}~> ?x |- _ =>
                          match goal with
                          | H : f =[C] id[x] |- _ => fail 1
                          | _ =>  let EQ_hom := fresh "EQ_hom" in
                                  pose proof (discrete_hom_eq f) as EQ_hom;
                                  tryif (depdes EQ_hom) then (try clear f) else (try clear f EQ_hom)
                          end 
                      | f : ?x ~> ?y |- _ =>
                          match goal with
                          | _ : x = y |- _ => fail 1
                          | _ : y = x |- _ => fail 1
                          | _ =>  let EQ_obj := fresh "EQ_obj" in
                                  pose proof (discrete_obj_eq f) as EQ_obj;
                                  try depdes EQ_obj
                          end
                      end.

Ltac common_simpl_prep_hook_category ::= deal_discrete.