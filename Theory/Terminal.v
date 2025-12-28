Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.

Generalizable All Variables.

Section Definitions.
  Context {C : Category}.
  
  (** An object [T] is said to be a terminal object in [C] if for every object [X]
    * in [C], there exists a unique morphism from [X] to [T].
    *)
  Class Terminal (T : C) :=
    { terminal_morphism X : X ~> T
    ; terminal_unique X (f g : X ~> T) : f ≡ g
    }.

  (** An object [I] is said to be an initial object in [C] if for every object [X]
    * in [C], there exists a unique morphism from [I] to [X].
    *)
  Class Initial (I : C) :=
    { initial_morphism X : I ~> X
    ; initial_unique X (f g : I ~> X) : f ≡ g
    }.
End Definitions.

Arguments terminal_morphism {_%_category_scope _%_object_scope _} _%_object_scope.
Arguments terminal_unique {_%_category_scope _%_object_scope _ _%_object_scope}
  _%_morphism_scope _%_morphism_scope.
Arguments initial_morphism {_%_category_scope _%_object_scope _} _%_object_scope.
Arguments initial_unique {_%_category_scope _%_object_scope _ _%_object_scope}
  _%_morphism_scope _%_morphism_scope.

Section Lemmas.
  Context {C : Category}.

  (* Every two terminal objects are isomorphic *)
  Definition terminal_iso {T1 T2 : C}
    : Terminal T1 → Terminal T2 → T1 ≅ T2.
  Proof.
    intros; isomorphism.
    3,4: apply terminal_unique.
    all: now apply terminal_morphism.
  Qed.

  (* Every two initial objects are isomorphic *)
  Definition initial_iso {I1 I2 : C}
    : Initial I1 → Initial I2 → I1 ≅ I2.
  Proof.
    intros; isomorphism.
    3,4: apply initial_unique.
    all: now apply initial_morphism.
  Qed.
End Lemmas.

(** An object [Z] is said to be a zero object in [C] if it is both terminal and
  * initial.
  *)
Section ZeroObject.
  Class HasZeroObjects (C : Category) :=
    { zero : C
    ; zero_terminal : Terminal zero
    ; zero_initial : Initial zero
    }.

  Definition zero_morphism
    {C : Category} {ZERO : HasZeroObjects C} {X Y : C} : X ~> Y :=
      @initial_morphism C zero zero_initial Y
    ∘ @terminal_morphism C zero zero_terminal X.

  Local Notation "'0'" := zero : object_scope.
  Local Notation "'0'" := zero_morphism : morphism_scope.

  Section Lemmas.
    Context {C : Category} {ZERO : HasZeroObjects C}.
    
    Lemma zero_absorb_right {X Y Z : C} (f : X ~> Y)
      : 0 ∘ f << X ~~> Z >> 0.
    Proof.
      unfold zero_morphism. comp_left.
      srapply terminal_unique.
      apply zero_terminal.
    Qed.

    Lemma zero_absorb_left {X Y Z : C} (f : Y ~> Z)
      : f ∘ 0 << X ~~> Z >> 0.
    Proof.
      unfold zero_morphism. comp_right.
      srapply initial_unique.
      apply zero_initial.
    Qed.
  End Lemmas.
End ZeroObject.

#[export] Existing Instance zero_terminal.
#[export] Existing Instance zero_initial.

Notation "'0'" := zero : object_scope.
Notation "'0[' C ']'" := (@zero C%category _)
  (at level 0, only parsing) : object_scope.

Notation "'0'" := zero_morphism : morphism_scope.
Notation "'0{' x '~>' y '}'" := (@zero_morphism _ _ x y) 
  (only parsing) : morphism_scope.