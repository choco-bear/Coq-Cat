Require Import Category.Lib.Tactics.

Generalizable All Variables.
Set Universe Polymorphism.

(** Group *)
Record Group :=
  { grp_carrier : Type
  ; grp_setoid  : Setoid grp_carrier
  ; grp_op      : Operation grp_carrier

  ; grp_id    : grp_carrier
  ; grp_id_l  : ∀ x, op grp_id x ≡ x
  ; grp_id_r  : ∀ x, op x grp_id ≡ x

  ; grp_inv   : grp_carrier → grp_carrier
  ; grp_inv_l : ∀ x, op (grp_inv x) x ≡ grp_id
  ; grp_inv_r : ∀ x, op x (grp_inv x) ≡ grp_id

  ; grp_assoc : ∀ x y z, op (op x y) z ≡ op x (op y z)
  }.
Coercion grp_carrier : Group >-> Sortclass.
#[export] Existing Instance grp_setoid.
#[export] Existing Instance grp_op.
Arguments grp_id {G} : rename.
Arguments grp_inv {G} g : rename.

#[export] Hint Rewrite @grp_id_l @grp_id_r @grp_inv_l @grp_inv_r : grp_simplify.

Declare Scope group_scope.
Bind Scope group_scope with Group.
Delimit Scope group_scope with group.

Record GroupHomomorphism {G : Group} {G' : Group} :=
  { grp_map :> G → G'
  ; grp_map_respects : Proper (equiv ==> equiv) grp_map
  ; grp_map_op : ∀ g h, grp_map (op g h) ≡ op (grp_map g) (grp_map h)
  }.
#[export] Existing Instance grp_map_respects.
Arguments grp_map_op {G G' φ} (g h)%_group_scope : rename.
Arguments GroupHomomorphism (G G') : clear implicits.

#[export] Program Instance group_hom_setoid {G : Group} {G' : Group}
  : Setoid (GroupHomomorphism G G') := {| equiv := λ φ ψ, ∀ g, φ g ≡ ψ g |}.
Next Obligation.
  now equivalence; transitivity (y g).
Qed.

Program Definition grp_id_map (G : Group) :=
  {| grp_map := Datatypes.id |}.
Next Obligation. done. Qed.

Program Definition grp_hom_comp {G : Group} {G' : Group} {G'' : Group}
  (φ : GroupHomomorphism G' G'') (ψ : GroupHomomorphism G G')
  : GroupHomomorphism G G'' := {|  grp_map := λ g, φ (ψ g) |}.
Next Obligation. now proper; rewrite X. Qed.
Next Obligation. now rewrite !grp_map_op. Qed.

Notation "x ⋅ y" := (@op _ _ (grp_op _) x%group y%group)
  (at level 40, left associativity) : group_scope.
Notation "'(⋅)'" := (@op _ _ (grp_op _)) (only parsing) : group_scope.
Notation "'(' x '⋅)'" := (@op _ _ (grp_op _) x%group) (only parsing) : group_scope.
Notation "'(⋅' x ')'" := (λ y, @op _ _ (grp_op _) y x%group)
  (only parsing) : group_scope.
Notation "x '⋅[' G ']' y" :=
  (@op G%group (grp_setoid G%group) (grp_op G%group) x%group y%group)
  (at level 40) : group_scope.

Notation "'ε'" := grp_id : group_scope.
Notation "'ε[' G ']'" := (@grp_id G) (only parsing) : group_scope.

Notation "x '⁻¹'" := (grp_inv x%group) (at level 9) : group_scope.
Notation "'(⁻¹)'" := grp_inv (only parsing) : group_scope.

Local Open Scope group_scope.

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
  
  Tactic Notation "__grp_simplify" := autorewrite with grp_simplify.
  Tactic Notation "__grp_simplify" "in" hyp(H) := autorewrite with grp_simplify in H.
  Tactic Notation "__grp_simplify" "in" "*" := autorewrite with grp_simplify in *.

  Tactic Notation "grp_simplify" := repeat rewrite <-grp_assoc; __grp_simplify.
  Tactic Notation "grp_simplify" "in" hyp(H) :=
    repeat rewrite <-grp_assoc in H; __grp_simplify in H.
  Tactic Notation "grp_simplify" "in" "*" :=
    repeat rewrite <-grp_assoc in *; __grp_simplify in *.
End BasicGrpTactics.
Export BasicGrpTactics.

Section group.
  Context {G : Group}.
  Implicit Types x y z : G.
  
  Lemma grp_cancel_l x y z : x ⋅ z ≡ y ⋅ z → x ≡ y.
  Proof.
    intro. op_right (z⁻¹) in X.
    now __grp_simplify in X.
  Qed.
  Lemma grp_cancel_r x y z : x ⋅ y ≡ x ⋅ z → y ≡ z.
  Proof.
    intro. op_left (x⁻¹) in X.
    now __grp_simplify in X.
  Qed.

  Lemma grp_id_unique_l e x : e ⋅ x ≡ x → e ≡ ε.
  Proof. now intro H; op_right (x⁻¹) in H; __grp_simplify in H. Qed.
  Lemma grp_id_unique_r e x : x ⋅ e ≡ x → e ≡ ε.
  Proof. now intro H; op_left (x⁻¹) in H; __grp_simplify in H. Qed.

  Lemma grp_inv_unique_r x y : x ⋅ y ≡ ε → y ≡ x⁻¹.
  Proof. now intro H; op_left (x⁻¹) in H; __grp_simplify in H. Qed.
  Lemma grp_inv_unique_l x y : x ⋅ y ≡ ε → x ≡ y⁻¹.
  Proof. now intro H; op_right (y⁻¹) in H; __grp_simplify in H. Qed.

  Lemma inv_involutive x : (x⁻¹)⁻¹ ≡ x.
  Proof. rewrite <-grp_inv_unique_r; [done|now __grp_simplify]. Qed.

  Lemma id_inv_id : ε⁻¹ ≡ ε[G].
  Proof. now symmetry; apply grp_inv_unique_r; __grp_simplify. Qed.

  Lemma grp_inv_simpl_1 x y : x ⋅ y ⋅ y⁻¹ ≡ x.
  Proof. now rewrite grp_assoc; __grp_simplify. Qed.
  Lemma grp_inv_simpl_2 x y : x ⋅ y⁻¹ ⋅ y ≡ x.
  Proof. now rewrite grp_assoc; __grp_simplify. Qed.
End group.
#[export] Hint Rewrite @inv_involutive @id_inv_id
                       @grp_inv_simpl_1 @grp_inv_simpl_2 : grp_simplify.

Section homomorphism.
  Context {G : Group} {G' : Group}.
  Context {φ : GroupHomomorphism G G'}.

  Lemma grp_id_map_left : grp_hom_comp (grp_id_map G') φ ≡ φ.
  Proof. done. Qed.
  Lemma grp_id_map_right : grp_hom_comp φ (grp_id_map G) ≡ φ.
  Proof. done. Qed.

  Lemma homomorphism_id : φ ε ≡ ε.
  Proof. now eapply grp_id_unique_l; rewrite <-grp_map_op; __grp_simplify. Qed.

  Lemma homomorphism_inverse_natural x : φ (x⁻¹) ≡ (φ x)⁻¹.
  Proof.
    apply grp_inv_unique_r.
    rewrite <-grp_map_op; __grp_simplify.
    apply homomorphism_id.
  Qed.
End homomorphism.
#[export] Hint Rewrite @homomorphism_id @homomorphism_inverse_natural : grp_simplify.

#[export] Program Instance grp_hom_comp_respects
  {G : Group} {G' : Group} {G'' : Group}
  : Proper (equiv ==> equiv ==> equiv) (@grp_hom_comp G G' G'') :=
    λ φ ψ Hφψ φ' ψ' Hφψ', _.
Next Obligation. now rewrite Hφψ', Hφψ. Qed.

(** Abelian Group *)
Record AbGroup :=
  { ab_grp :> Group 
  ; ab_comm : Commutative (grp_op ab_grp)
  }.
#[export] Existing Instance ab_comm.

Record IsSubGroupProperty {G : Group} (P : G → Type) :=
  { nonempty      : P ε
  ; op_closed x y : P x → P y → P (x ⋅ y)
  ; inv_closed x  : P x → P (x⁻¹)
  }.

Local Obligation Tactic := cat_simpl; grp_simplify; simpl; try done.
Program Definition mk_subgroup {G : Group} (P : G → Type)
  : IsSubGroupProperty P → Group := λ SGP,
    {|  grp_setoid := {grp_setoid G & P}

      ; grp_op := {| op := λ X Y, (`1 X ⋅ `1 Y; op_closed P SGP _ _ (`2 X) (`2 Y)) |}
      ; grp_id := (ε; nonempty P SGP)
      ; grp_inv := λ X, ((`1 X)⁻¹; inv_closed P SGP _ (`2 X))
    |}.
Next Obligation. now proper; rewrite X, X0. Qed.

Program Definition center (G : Group) : AbGroup :=
  {| ab_grp := mk_subgroup (λ g : G, ∀ h, g ⋅ h ≡ h ⋅ g) {| nonempty := _ |} |}.
Next Obligation. now rewrite <-X, !grp_assoc, X0. Qed.
Next Obligation. now specialize (X (x⁻¹ ⋅ h ⋅ x⁻¹)); grp_simplify in X. Qed.
Next Obligation. now construct; destruct x, y. Qed.