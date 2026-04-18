Require Import CommonTactics CommonFacts.
Require Import Category CategoryTactics CategoryFacts.
Require Import Functor FunctorTactics FunctorFacts.
Require Import Morphism.

Local Open Scope morphism_scope.

Lemma left_cancel `{C : Category Obj} [x y z : Obj] (f g : x ~> y) (h : y ~> z) `{!Monic h}
  : h ∘ f =[C] h ∘ g → f = g.
Proof. common_simpl. Qed.

Lemma right_cancel `{C : Category Obj} [x y z : Obj] (f g : y ~> z) (h : x ~> y) `{!Epic h}
  : f ∘ h =[C] g ∘ h → f = g.
Proof. by apply epic. Qed.

Tactic Notation "comp_l" uconstr(p) :=
  autorewrite with assoc_right; unshelve simple refine (left_cancel _ _ p _); autorewrite with assoc_left.

Tactic Notation "cancel_l" uconstr(p) "in" hyp(H) :=
  match type of H with
  | @eq ?A ?f ?g => unshelve eapply (left_cancel _ _ p) in H; autorewrite with assoc_left in H
  | @eq ?A ?f ?g => fail 1 "The hypothesis" H "is not an equality between morphisms, or the term" p "is not appropriate"
  | _ => fail 1 "The hypothesis" H "is not an equality"
  end.

Tactic Notation "cancel_l" uconstr(p) "in" hyp(H) "as" ident(name) :=
  match type of H with
  | @eq ?A ?f ?g => unshelve eapply (left_cancel _ _ p) in H as name; autorewrite with assoc_left in name
  | @eq ?A ?f ?g => fail 1 "The hypothesis" H "is not an equality between morphisms, or the term" p "is not appropriate"
  | _ => fail 1 "The hypothesis" H "is not an equality"
  end.

Tactic Notation "comp_r" uconstr(p) :=
  autorewrite with assoc_left; unshelve simple refine (right_cancel _ _ p _); autorewrite with assoc_left.

Tactic Notation "cancel_r" uconstr(p) "in" hyp(H) :=
  match type of H with
  | @eq ?A ?f ?g => autorewrite with assoc_right in H; unshelve eapply (right_cancel _ _ p) in H; autorewrite with assoc_left in H
  | @eq ?A ?f ?g => fail 1 "The hypothesis" H "is not an equality between morphisms, or the term" p "is not appropriate"
  | _ => fail 1 "The hypothesis" H "is not an equality"
  end.

Tactic Notation "cancel_r" uconstr(p) "in" hyp(H) "as" ident(name) :=
  match type of H with
  | @eq ?A ?f ?g => autorewrite with assoc_right in H; unshelve eapply (right_cancel _ _ p) in H as name; autorewrite with assoc_left in H; autorewrite with assoc_left in name
  | @eq ?A ?f ?g => fail 1 "The hypothesis" H "is not an equality between morphisms, or the term" p "is not appropriate"
  | _ => fail 1 "The hypothesis" H "is not an equality"
  end.

Tactic Notation "split_idempotent" uconstr(p) := rewrite -(@split_comp_orig _ _ _ p).
Tactic Notation "split_idempotent" uconstr(p) "in" hyp(H) := rewrite -(@split_comp_orig _ _ _ p) in H.

Ltac smart_constructor_hook_morphism ::=  match goal with
                                          | |- SplitIdempotent ?f =>
                                              eapply mk_SplitIdempotent
                                          end.