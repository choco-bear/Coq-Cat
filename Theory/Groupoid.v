Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Lib.Algebra.

Generalizable All Variables.

Class Groupoid (C : Category) :=
  { every_is_iso x y (f : x ~> y) : IsIsomorphism f }.
#[export] Existing Instance every_is_iso.

Section Lemmas.
  Context `{GRPoid : @Groupoid G}.
  
  Lemma groupoid_cancel_r `(f : y ~{G}~> z) g `(h : x ~{G}~> y)
    : f ∘ h ≡ g ∘ h → f ≡ g.
  Proof using GRPoid.
    intros. remember (IsIsoToIso h _) as H. 
    replace h with (to H) in X by now rewrite HeqH.
    comp_right (H⁻¹) in X. now normalize in X.
  Qed.

  Lemma groupoid_cancel_l `(g : x ~{G}~> y) h `(f : y ~{G}~> z)
    : f ∘ g ≡ f ∘ h → g ≡ h.
  Proof using GRPoid.
    intros. remember (IsIsoToIso f _) as F.
    replace f with (to F) in X by now rewrite HeqF.
    comp_left (F⁻¹) in X. now normalize in X.
  Qed.
End Lemmas.

Section Groups.
  Local Open Scope group_scope.

  Definition of_group (G : Group) : Category :=
    {|  obj := poly_unit
      ; hom := λ _ _, G

      ; id      := λ _, ε
      ; compose := λ _ _ _, (⋅)

      ; id_left  := λ _ _, grp_id_l G
      ; id_right := λ _ _, grp_id_r G

      ; comp_assoc     := λ _ _ _ _ f g h, symmetry (grp_assoc G f g h)
      ; comp_assoc_sym := λ _ _ _ _, grp_assoc G
    |}.

  #[export] Program Instance groupoid_of_group (G : Group) : Groupoid (of_group G).
  Next Obligation. construct; [|apply grp_inv_r|apply grp_inv_l]. Qed.
End Groups.

Coercion of_group : Group >-> Category.