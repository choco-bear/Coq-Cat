Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

Inductive ParObj : Set := ParA | ParB.

Inductive ParHom : bool → ParObj → ParObj → Set :=
  | ParIdA : ParHom true ParA ParA
  | ParIdB : ParHom true ParB ParB
  | ParF : ParHom true ParA ParB
  | ParG : ParHom false ParA ParB.
#[export] Hint Constructors ParHom : parallel_laws.

Definition ParHom_inv_t : ∀ b x y, ParHom b x y → Type.
  intros [] [] [] f.
  - exact (f = ParIdA).
  - exact (f = ParF).
  - exact poly_void.
  - exact (f = ParIdB).
  - exact poly_void.
  - exact (f = ParG).
  - exact poly_void.
  - exact poly_void.
Defined.

Corollary ParHom_inv {b x y} f : ParHom_inv_t b x y f.
Proof. now destruct f. Qed.

Lemma ParHom_Id_false_absurd : ∀ x, ¬ ParHom false x x.
Proof. intros []; exact ParHom_inv. Qed.
Lemma ParHom_B_A_absurd : ∀ b, ¬ ParHom b ParB ParA.
Proof. intros []; exact ParHom_inv. Qed.

#[export] Hint Extern 4 =>
  match goal with
  | [ H : ParHom false ?X ?X |- _ ] => contradiction (ParHom_Id_false_absurd X)
  | [ H : ParHom ?b ParB ParA |- _ ] => contradiction (ParHom_B_A_absurd b)
  end : parallel_laws.

Local Ltac parallel_solver :=
  intros; repeat match goal with
                 | [ f : ParHom _ _ _ |- _ ] => srewrite (ParHom_inv f)
                 | [ x : ParObj |- _ ] => destruct x
                 | [ H : ParB = ParA |- _ ] => inversion H
                 | [ H : ParA = ParB |- _ ] => inversion H
                 | [ |- Equivalence _ ] => equivalence
                 end; cat_simpl; eauto with parallel_laws.

(** This is the category with two objects and two parallel morphisms between them
  * (and two identity morphisms):
  *
  *       ---f--->
  *    A            B
  *       ---g--->
  *
  *)
Program Definition Parallel : Category :=
  {| obj := ParObj
   ; hom := λ x y, ∃ b, ParHom b x y
   ; homset := λ X Y,
      {| equiv := λ f g, `1 f = `1 g
       ; setoid_equiv := _
      |}
   ; id := λ x, match x with
                | ParA => (true; ParIdA)
                | ParB => (true; ParIdB)
                end
   |}.
Next Obligation. parallel_solver. (* SLOW *) Defined.
Next Obligation. parallel_solver. Qed.
Next Obligation. parallel_solver. Qed.
Next Obligation. destruct f; parallel_solver. Qed.
Next Obligation. parallel_solver. Qed.
Next Obligation. parallel_solver. Qed.