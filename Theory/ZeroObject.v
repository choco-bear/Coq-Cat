Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Terminal.
Require Import Category.Theory.Initial.

Generalizable All Variables.

(** An object [Z] is said to be a zero object in [C] if it is both terminal and
  * initial.
  *)
Section ZeroObject.
  Class HasZeroObjects (C : Category) :=
    { zero : C
    ; zero_terminal : IsTerminal zero
    ; zero_initial : IsInitial zero
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