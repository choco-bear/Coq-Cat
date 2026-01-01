Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

(** A morphism [f] is said to be idempotent if [f ∘ f ≡ f]. *)
Class Idempotent `(f : x ~{C}~> x) := { idempotent : f ∘ f ≡ f }.

Class Split `(f : x ~{C}~> x) :=
  { other : C
  ; split_epic : x ~> other
  ; split_monic : other ~> x
  ; splits : split_monic ∘ split_epic ≡ f
  ; split_inverse : split_epic ∘ split_monic ≡ id
  }.

(** A morphism [f] is said to be involutive if [f ∘ f ≡ id]. *)
Class Involutive `(f : x ~{C}~> x) := { involutive : f ∘ f ≡ id }.

(** A morphism is an epimorphism if it is right-cancellable. *)
Class Epic `(f : x ~{C}~> y) := 
  { epic : ∀ z (g1 g2 : y ~> z), g1 ∘ f ≡ g2 ∘ f → g1 ≡ g2 }.

(** A morphism is a monomorphism if it is left-cancellable. *)
Class Monic `(f : x ~{C}~> y) := 
  { monic : ∀ z (g1 g2 : z ~> x), f ∘ g1 ≡ f ∘ g2 → g1 ≡ g2 }.

(** A morphism is a bimorphism if it is both an epimorphism and a monomorphism. *)
Definition BiMorphic `(f : x ~{C}~> y) := Epic f * Monic f.
#[export] Hint Unfold BiMorphic : core.

(** A morphism [f : a ~> b] is regular if there is a morphism [g : b ~> a] such
  * that [f ∘ g ∘ f ≡ f]. *)
Class Regular `(f : x ~{C}~> y) :=
  { pseudo_inverse : y ~> x
  ; regular : f ∘ pseudo_inverse ∘ f ≡ f
  }.

Section Proper.
  Context {C : Category}.

  #[export]
  Instance proper_epic {x y : C} : Proper (equiv ==> iffT) (@Epic C x y).
  Proof.
    proper; split; ss; apply epic
    ; solve [now rewrite X|now rewrite <-X].
  Qed.

  #[export]
  Instance proper_monic {x y : C} : Proper (equiv ==> iffT) (@Monic C x y).
  Proof.
    proper; split; ss; apply monic
    ; solve [now rewrite X|now rewrite <-X].
  Qed.

  #[export]
  Instance proper_idempotent {x : C} : Proper (equiv ==> iffT) (@Idempotent _ x).
  Proof.
    proper; inversion X0; construct
    ; solve [now rewrite X|now rewrite <-X].
  Qed.
End Proper.

#[export]
Instance split_idempotent `(@Split C x f) : Idempotent f.
Proof.
  rewrite <-splits; construct.
  by comp_left; rewrite comp_assoc, split_inverse.
Qed.

(** Lemmas about identity morphisms *)
Section Id.
  Context {C : Category}.

  Corollary id_epic {x : C} : Epic id[x].
  Proof. construct. now rewrite !id_right in X. Qed.

  Corollary id_monic {x : C} : Monic id[x].
  Proof. construct. now rewrite !id_left in X. Qed.

  Corollary id_bimorphic {x : C} : BiMorphic id[x].
  Proof. split; [apply id_epic|apply id_monic]. Qed.
End Id.

(** Lemmas about inverse morphisms *)
Section Inverse.
  Context `{f : x ~{C}~> y}.

  Lemma has_right_inverse_epic
    : (∃ g, f ∘ g ≡ id) → Epic f.
  Proof.
    intros [g EQ]. construct.
    rewrite <-id_right, <-(id_right g2).
    by rewrite <-EQ, !comp_assoc.
  Qed.

  Lemma has_right_inverse_regular
    : (∃ g, f ∘ g ≡ id) → Regular f.
  Proof. by intros [g EQ]; construct; [exact g|rewrite EQ]. Qed.

  Lemma has_left_inverse_monic
    : (∃ g, g ∘ f ≡ id) → Monic f.
  Proof.
    intros [g EQ]. construct.
    rewrite <-id_left, <-(id_left g2).
    by rewrite <-EQ, <-!comp_assoc.
  Qed.

  Lemma has_left_inverse_regular
    : (∃ g, g ∘ f ≡ id) → Regular f.
  Proof. by intros [g EQ]; construct; [exact g|rewrite <-comp_assoc, EQ]. Qed.
End Inverse.

(** Lemmas about composition of morphisms *)
Section Composition.
  Context `{f : y ~{C}~> z} `{g : x ~{C}~> y}.

  Definition epic_compose
    : Epic f → Epic g → Epic (f ∘ g).
  Proof.
    construct. do 2 apply epic.
    now rewrite <-!comp_assoc.
  Qed.

  Definition epic_erase
    : Epic (f ∘ g) → Epic f.
  Proof. construct. comp_right g in X0. by apply epic. Qed.

  Definition monic_compose
    : Monic f → Monic g → Monic (f ∘ g).
  Proof.
    construct. do 2 apply monic.
    now rewrite !comp_assoc.
  Qed.

  Definition monic_erase
    : Monic (f ∘ g) → Monic g.
  Proof. construct. comp_left f in X0. by apply monic. Qed.
End Composition.