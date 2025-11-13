Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Functor.Setoid.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.
Require Import Category.Construction.Fun.

Generalizable All Variables.

Inductive TwoObj@{o} : Type@{o} := TwoA | TwoB.

Inductive TwoHom@{o h} : TwoObj@{o} → TwoObj@{o} → Type@{h} :=
  | TwoIdA : TwoHom TwoA TwoA
  | TwoIdB : TwoHom TwoB TwoB
  | TwoF   : TwoHom TwoA TwoB
  .
#[export] Hint Constructors TwoHom : two_laws.

Definition TwoHom_inv_t : ∀ x y, TwoHom x y → Prop.
  intros [] [] f.
  - exact (f = TwoIdA).
  - exact (f = TwoF).
  - exact False.
  - exact (f = TwoIdB).
Defined.

Corollary TwoHom_inv {x y} f : TwoHom_inv_t x y f.
Proof. now destruct f. Qed.

Lemma TwoHom_B_A_absurd : ¬ TwoHom TwoB TwoA.
Proof. exact TwoHom_inv. Qed.

#[export] Hint Extern 4 => contradiction TwoHom_B_A_absurd : two_laws.

Local Ltac two_solver :=
  intros; repeat match goal with
                 | [ f : TwoHom _ _ |- _ ] => srewrite (TwoHom_inv f)
                 | [ x : TwoObj |- _ ] => destruct x
                 | [ H : TwoB = TwoA |- _ ] => inversion H
                 | [ H : TwoA = TwoB |- _ ] => inversion H
                 end; auto with two_laws.

(** The category 2 has two objects, their identity morphisms, and one morphism from
  * the first object to the second object.
  *)
Program Definition _2@{o h p} : Category@{o h p} :=
  {| obj    := TwoObj@{o}
   ; hom    := TwoHom@{o h}
   ; homset := Morphism_equality
   ; id     := λ x, match x with
                    | TwoA => TwoIdA
                    | TwoB => TwoIdB
                    end
  |}.
Next Obligation. two_solver. Defined.
Next Obligation. two_solver. Qed.
Next Obligation. two_solver. Qed.
Next Obligation. two_solver. Qed.
Next Obligation. two_solver. Qed.

Notation "2" := _2 : category_scope.

Section Correspondence.
  Polymorphic Universes o h p.
  Context {C : Category@{o h p}}.

  (** There is a one-to-one correspondence between morphisms of [C] and functors
    * from [2] to [C]. *)
  Program Definition Wrap {x y : C} (f : x ~{C}~> y) : 2 ⟶ C :=
    {| fobj := λ o, match o with
                    | TwoA => x
                    | TwoB => y
                    end
     ; fmap := λ _ _ ϕ, match ϕ with
                        | TwoIdA => id[x]
                        | TwoIdB => id[y]
                        | TwoF   => f
                        end
    |}.
  Next Obligation. now two_solver. Qed.
  Next Obligation. two_solver; cat. Qed.
  
  Definition Unwrap (F : 2 ⟶ C) : F TwoA ~> F TwoB := fmap[F] TwoF.

  (*
  Lemma Wrap_Unwrap (F : 2 ⟶ C) : Wrap (Unwrap F) ≡ F.
  Proof.
  Admitted.
  *)
End Correspondence.