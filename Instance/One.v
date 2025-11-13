Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Functor.Setoid.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.
Require Import Category.Construction.Fun.

Generalizable All Variables.

(** The one category, with one object, one morphism. Also called the trivial
  * category or singleton category.
  *)

Program Definition _1 : Category := 
  {| obj := poly_unit
   ; hom := fun _ _ => poly_unit
   ; homset := Morphism_equality
   ; id := fun _ => ttt
   ; compose := fun _ _ _ _ _ => ttt
  |}.

Notation "1" := _1 : category_scope.

(** The unique functor to one category from any other category. *)
#[export]
Program Instance Erase `(C : Category) : C ⟶ 1 :=
  {| fobj := fun _ => ttt
   ; fmap := fun _ _ _ => id
  |}.

Section Correspondence.
  Context {C : Category}.

  (** There is a one-to-one correspondence between objects of [C] and functors
    * from [1] to [C]. *)
  Program Definition Wrap (x : C) : 1 ⟶ C :=
    {| fobj := λ _, x
     ; fmap := λ _ _ _, id[x]

     ; fmap_respects := λ _ y f g fg, reflexivity id[x]
     ; fmap_id := λ _, reflexivity id[x]
     ; fmap_comp := λ _ _ _ f g, symmetry (id_right id[x])
    |}.
  
  Definition Unwrap (F : 1 ⟶ C) : C := F ttt.

  Lemma Wrap_Unwrap (F : 1 ⟶ C) : Wrap (Unwrap F) ≡ F.
  Proof. srapply Component_Is_Iso_NatIso; construct; cat. Qed.

  Lemma Unwrap_Wrap (x : C) : Unwrap (Wrap x) = x.
  Proof. reflexivity. Qed.
End Correspondence.