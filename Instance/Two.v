Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

Inductive TwoObj : Set := TwoA | TwoB.

Inductive TwoHom : TwoObj → TwoObj → Set :=
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
Program Definition _2 : Category :=
  {| obj := TwoObj
   ; hom := TwoHom
   ; homset := Morphism_equality
   ; id := λ x, match x with
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