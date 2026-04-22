Require Import CommonTactics CommonFacts Category.
Require Import Functor FunctorTactics FunctorFacts.

Structure NatTrans `{C : Category ObjC} `{D : Category ObjD} {F G : C ⟶ D} := mk_NatTrans {
  component :> ∀ x, F x ~> G x;
  naturality {x y} (f : x ~> y) : component y ∘ (F # f) =[D] (G # f) ∘ component x
}.

Declare Scope nat_trans_scope.
Delimit Scope nat_trans_scope with nat_trans.
Bind Scope nat_trans_scope with NatTrans.

Arguments NatTrans {ObjC%_type_scope C%_category_scope ObjD%_type_scope D%_category_scope} (F G)%_functor_scope : rename.
Arguments mk_NatTrans {ObjC%_type_scope C%_category_scope ObjD%_type_scope D%_category_scope} {F G}%_functor_scope (_ _)%_function_scope.
Arguments component {ObjC%_type_scope C%_category_scope ObjD%_type_scope D%_category_scope} {F G}%_functor_scope x%_object_scope : rename, simpl never.

Notation "F ⟹ G" := (NatTrans F G) (at level 70, no associativity, format "F  ⟹  G") : type_scope.
Notation "F '⟹@{' C ',' D '}' G" := (@NatTrans _ C%category _ D%category F%functor G%functor)
  (at level 70, no associativity, only parsing) : type_scope.

Program Definition IdNatTrans `{C : Category ObjC} `{D : Category ObjD} (F : C ⟶ D)
  : F ⟹ F := {| component := λ x, id[F x] |}%morphism.

Program Definition NatTransVerComp `{C : Category ObjB} `{D : Category ObjC} {F G K : C ⟶ D} (τ : G ⟹ K) (μ : F ⟹ G)
  : F ⟹ K := {| component := λ x, τ x ∘ μ x |}%morphism.
Next Obligation. rewrite -comp_assoc naturality comp_assoc naturality //. Qed.

Notation "'id'" := (IdNatTrans _) (at level 0, no associativity, only parsing) : nat_trans_scope.
Notation "'id[' F ']'" := (IdNatTrans F%functor) (at level 9, no associativity, format "id[ F ]") : nat_trans_scope.
Notation "τ ▪ μ" := (NatTransVerComp τ% nat_trans μ%nat_trans) (at level 40, left associativity) : nat_trans_scope.

Section NatTransComponent.
  Context `{C : Category ObjC} `{D : Category ObjD}.
  
  Lemma IdNatTransComponent (F : C ⟶ D) x : id[F]%nat_trans x = id[F x]%morphism.
  Proof. reflexivity. Qed.

  Lemma NatTransVerCompComponent {F G K : C ⟶ D} (τ : G ⟹ K) (μ : F ⟹ G) x
    : (τ ▪ μ)%nat_trans x = (τ x ∘ μ x)%morphism.
  Proof. reflexivity. Qed.
End NatTransComponent.
#[export] Hint Rewrite @IdNatTransComponent @NatTransVerCompComponent : normalize.

Lemma nat_trans_ext `{C : Category ObjC} `{D : Category ObjD} {F G : C ⟶ D} (τ μ : F ⟹ G)
  : (∀ x, τ x =[D] μ x) → τ = μ.
Proof.
  rewrite /component. depdes τ μ. i. apply func_ext_dep in H as <-.
  by assert (naturality0 = naturality1) as <- by apply proof_irr.
Qed.