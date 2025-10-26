Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

Module Defs.
  (** A setoid object is a type equipped with an equivalence relation. *)
  Record SetoidObject@{o p} : Type@{max(o+1,p+1)} :=
    { carrier :> Type@{o}
    ; is_setoid :> Setoid@{o p} carrier
    }.
  #[export] Existing Instance is_setoid.

  (** A setoid morphism is a function between setoid objects that respects the
    * equivalence relations on the source and target setoids.
    *)
  Record SetoidMorphism@{o h p} `{Setoid@{o p} x} `{Setoid@{o p} y} :=
    { morphism :> x → y
    ; proper_morphism :> Proper@{h p} (respectful@{h p h p h p} equiv equiv) morphism
    }.
  #[export] Existing Instance proper_morphism.

  Arguments SetoidMorphism {_} _ {_} _.
  Arguments morphism {_ _ _ _ _} _.

  (** Equivalence relation over the setoid morphisms is defined as functional
    * extensionality. *)
  Definition SetoidMorphism_equiv@{o h p} {x y : SetoidObject@{o p}}
    : crelation@{h p} (SetoidMorphism@{o h p} x y) :=
      λ f g, ∀ a, @equiv@{o p} _ y (f a) (g a).

  Arguments SetoidMorphism_equiv {x y} _ _ /.

  (** Setoid structure on the setoid morphisms. *)
  #[export]
  Program Instance SetoidMorphism_Setoid@{o h p} {x y : SetoidObject@{o p}}
    : Setoid@{h p} (SetoidMorphism@{o h p} x y) :=
      {| equiv := SetoidMorphism_equiv@{o h p} |}.
  Next Obligation. equivalence. now transitivity (y0 a). Qed.

  (** Identity morphism *)
  Definition SetoidMorphism_id@{o p} {x : SetoidObject@{o p}}
    : SetoidMorphism@{o p p} x x := {| morphism := Datatypes.id |}.
  #[export] Hint Unfold SetoidMorphism_id : core.

  (** Setoid morphism composition *)
  Program Definition SetoidMorphism_compose@{o h p}
    {x y z : SetoidObject@{o p}}
    (f : SetoidMorphism@{o h p} y z) (g : SetoidMorphism@{o h p} x y)
    : SetoidMorphism@{o h p} x z := {| morphism := λ a, f (g a) |}.
  Next Obligation. proper. now do 2 apply proper_morphism. Qed.
  #[export] Hint Unfold SetoidMorphism_compose : core.

  Program Definition SetoidMorphism_compose_respects@{o h p}
    {x y z : SetoidObject@{o p}}
    : Proper@{h p} (equiv@{h p} ==> equiv@{h p} ==> equiv@{h p})
      (@SetoidMorphism_compose@{o h p} x y z).
  Proof. proper. now rewrites. Qed.
End Defs.
Export Defs.

(** The category of setoids and setoid morphisms. *)
Program Definition Sets@{o so} : Category@{so o o} :=
  {| obj := SetoidObject@{o o} : Type@{so}
   ; hom := λ x y, SetoidMorphism@{o o o} x y : Type@{o}
   ; homset := @SetoidMorphism_Setoid@{o o o}
   ; id := @SetoidMorphism_id@{o o}
   ; compose := @SetoidMorphism_compose@{o o o}
   ; compose_respects := @SetoidMorphism_compose_respects@{o o o}
  |}.