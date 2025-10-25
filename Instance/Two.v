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

Corollary TwoHom_inv x y f : TwoHom_inv_t x y f.
Proof. now destruct f. Qed.

Lemma TwoHom_B_A_absurd : ∀ CONTRA : TwoHom TwoB TwoA, False.
Proof. exact (TwoHom_inv _ _). Qed.

#[export] Hint Extern 4 => contradiction TwoHom_B_A_absurd : two_laws.

Local Ltac obligation_solver :=
  intros; repeat match goal with
                 | [ x : TwoObj |- _ ] => destruct x
                 end; simplify; auto with two_laws;
  try match goal with
      | [ H : TwoB = TwoA |- _ ] => inversion H
      | [ H : TwoA = TwoB |- _ ] => inversion H
      end;
  try match goal with
      | [ f : TwoHom ?X ?Y |- _ ] => spose (TwoHom_inv _ _ f) as INV
      end; try now subst.

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
Next Obligation. obligation_solver. Defined.
Next Obligation. obligation_solver. Qed.
Next Obligation. obligation_solver. Qed.
Next Obligation. obligation_solver. Qed.
Next Obligation. obligation_solver. Qed.

Notation "2" := _2 : category_scope.