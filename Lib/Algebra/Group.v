Require Import Category.Lib.Tactics.

Generalizable All Variables.

Class Operation A `{Setoid A} :=
  { op        : A → A → A
  ; op_proper : Proper (equiv ==> equiv ==> equiv) op
  }.
#[export] Existing Instance op_proper.

Class Group G `(Operation G) :=
  { grp_id    : G
  ; grp_id_l  : ∀ x, op grp_id x ≡ x
  ; grp_id_r  : ∀ x, op x grp_id ≡ x

  ; grp_inv : G → G
  ; grp_inv_l : ∀ x, op (grp_inv x) x ≡ grp_id
  ; grp_inv_r : ∀ x, op x (grp_inv x) ≡ grp_id

  ; grp_assoc : ∀ x y z, op (op x y) z ≡ op x (op y z)
  }.
Arguments Group (G)%_type_scope {SETOID OPERATION} : rename.

Declare Scope group_scope.
Bind Scope group_scope with Group.
Delimit Scope group_scope with group.

Notation "x ⋅ y" := (op x%group y%group)
  (at level 40, left associativity) : group_scope.
Notation "'(⋅)'" := op (only parsing) : group_scope.
Notation "'(' x '⋅)'" := (op x%group) (only parsing) : group_scope.
Notation "'(⋅' x ')'" := (λ y, op y x%group) (only parsing) : group_scope.

Notation "'ε'" := grp_id : group_scope.

Notation "x '⁻¹'" := (grp_inv x%group) (at level 9) : group_scope.
Notation "'(⁻¹)'" := grp_inv (only parsing) : group_scope.

Module BasicGrpTactics.
  Tactic Notation "op_left" uconstr(t) "in" hyp(H) :=
    match type of H with
    | ?x ≡ ?y => unshelve eapply (op_proper t t _ x y) in H; [reflexivity|]
    end; rewrite <-!grp_assoc in H.

  Tactic Notation "op_right" uconstr(t) "in" hyp(H) :=
    match type of H with
    | ?x ≡ ?y =>
        let H' := fresh H in
        pose proof H as H'; clear H;
        (assert (H : op x t ≡ op y t)
          by now apply op_proper); clear H'
    end; rewrite !grp_assoc in H.
    
  Local Open Scope group_scope.
  
  Tactic Notation "grp_simplify" :=
    repeat match goal with
    | [ |- context[?x⁻¹ ⋅ ?x] ] => rewrite !grp_inv_l
    | [ |- context[?x ⋅ ?x⁻¹] ] => rewrite !grp_inv_r
    | [ |- context[ε ⋅ ?x] ]    => rewrite !grp_id_l
    | [ |- context[?x ⋅ ε] ]    => rewrite !grp_id_r
    end.

  Tactic Notation "grp_simplify" "in" hyp(H) :=
    repeat match type of H with
    | context[?x⁻¹ ⋅ ?x] => rewrite !grp_inv_l in H
    | context[?x ⋅ ?x⁻¹] => rewrite !grp_inv_r in H
    | context[ε ⋅ ?x]    => rewrite !grp_id_l in H
    | context[?x ⋅ ε]    => rewrite !grp_id_r in H
    end.

  Tactic Notation "grp_simplify" "in" "*" :=
    repeat match goal with
    | [ |- context[?x⁻¹ ⋅ ?x] ]       => rewrite !grp_inv_l in *
    | [ _ : context[?x⁻¹ ⋅ ?x] |- _ ] => rewrite !grp_inv_l in *
    | [ |- context[?x ⋅ ?x⁻¹] ]       => rewrite !grp_inv_r in *
    | [ _ : context[?x ⋅ ?x⁻¹] |- _ ] => rewrite !grp_inv_r in *
    | [ |- context[ε ⋅ ?x] ]          => rewrite !grp_id_l in *
    | [ _ : context[ε ⋅ ?x] |- _ ]    => rewrite !grp_id_l in *
    | [ |- context[?x ⋅ ε] ]          => rewrite !grp_id_r in *
    | [ _ : context[?x ⋅ ε] |- _ ]    => rewrite !grp_id_r in *
    end.
End BasicGrpTactics.
Export BasicGrpTactics.

Section group.
  Context `{Group G}.
  Implicit Types x y z : G.
  Local Open Scope group_scope.
  
  Lemma grp_cancel_l x y z : x ⋅ z ≡ y ⋅ z → x ≡ y.
  Proof.
    intro. op_right (z⁻¹) in X.
    now grp_simplify in X.
  Qed.
  Lemma grp_cancel_r x y z : x ⋅ y ≡ x ⋅ z → y ≡ z.
  Proof.
    intro. op_left (x⁻¹) in X.
    now grp_simplify in X.
  Qed.
End group.