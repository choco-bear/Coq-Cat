Require Import CommonTactics CommonFacts Category.
Require Import Functor FunctorTactics FunctorFacts.

Structure NatTrans `{C : Category ObjC} `{D : Category ObjD} {F G : C ⟶ D} := mk_NatTrans {
  component :> ∀ x : ObjC, F x ~> G x;
  naturality {x y} (f : x ~> y) : component y ∘ (F # f) =[D] (G # f) ∘ component x
}.

Declare Scope nat_trans_scope.
Delimit Scope nat_trans_scope with nat_trans.
Bind Scope nat_trans_scope with NatTrans.

Arguments NatTrans {ObjC%_type_scope C%_category_scope ObjD%_type_scope D%_category_scope} (F G)%_functor_scope : rename.
Arguments mk_NatTrans {ObjC%_type_scope C%_category_scope ObjD%_type_scope D%_category_scope} {F G}%_functor_scope (_ _)%_function_scope.
Arguments component {ObjC%_type_scope C%_category_scope ObjD%_type_scope D%_category_scope} {F G}%_functor_scope x%_object_scope : rename, simpl never.

Notation "F ⟹ G" := (NatTrans F G) (at level 70, no associativity) : type_scope.
Notation "F '⟹@{' C ',' D '}' G" := (@NatTrans _ C%category _ D%category F%functor G%functor)
  (at level 70, no associativity, format "F  ⟹@{ C , D }  G") : type_scope.