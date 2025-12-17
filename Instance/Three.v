Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

Inductive ThreeObj : Set := ThreeA | ThreeB | ThreeC.

Inductive ThreeHom : ThreeObj → ThreeObj → Set :=
  | ThreeIdA : ThreeHom ThreeA ThreeA
  | ThreeIdB : ThreeHom ThreeB ThreeB
  | ThreeIdC : ThreeHom ThreeC ThreeC
  | ThreeAB : ThreeHom ThreeA ThreeB
  | ThreeBC : ThreeHom ThreeB ThreeC
  | ThreeAC : ThreeHom ThreeA ThreeC
  .
#[export] Hint Constructors ThreeHom : three_laws.

Definition ThreeHom_inv_t : ∀ x y, ThreeHom x y → Type.
  intros [] [] f.
  - exact (f = ThreeIdA).
  - exact (f = ThreeAB).
  - exact (f = ThreeAC).
  - exact poly_void.
  - exact (f = ThreeIdB).
  - exact (f = ThreeBC).
  - exact poly_void.
  - exact poly_void.
  - exact (f = ThreeIdC).
Defined.

Corollary ThreeHom_inv {x y} f : ThreeHom_inv_t x y f.
Proof. now destruct f. Qed.

Lemma ThreeHom_B_A_absurd : ¬ ThreeHom ThreeB ThreeA.
Proof. exact ThreeHom_inv. Qed.
Lemma ThreeHom_C_A_absurd : ¬ ThreeHom ThreeC ThreeA.
Proof. exact ThreeHom_inv. Qed.
Lemma ThreeHom_C_B_absurd : ¬ ThreeHom ThreeC ThreeB.
Proof. exact ThreeHom_inv. Qed.
#[export] Hint Extern 4 => contradiction ThreeHom_B_A_absurd : three_laws.
#[export] Hint Extern 4 => contradiction ThreeHom_C_A_absurd : three_laws.
#[export] Hint Extern 4 => contradiction ThreeHom_C_B_absurd : three_laws.

Local Ltac three_solver :=
  intros; repeat match goal with
                 | [ f : ThreeHom _ _ |- _ ] => srewrite (ThreeHom_inv f)
                 | [ x : ThreeObj |- _ ] => destruct x
                 | [ H : ThreeC = ThreeA |- _ ] => inversion H
                 | [ H : ThreeC = ThreeB |- _ ] => inversion H
                 | [ H : ThreeB = ThreeA |- _ ] => inversion H
                 | [ H : ThreeA = ThreeB |- _ ] => inversion H
                 | [ H : ThreeA = ThreeC |- _ ] => inversion H
                 | [ H : ThreeB = ThreeC |- _ ] => inversion H
                 end; auto with three_laws.

(** The category 3 has three objects, their identity morphisms, and morphisms from
  * the first object to the second and third objects, and from the second object to
  * the third object.
  *)
Program Definition _3 : Category :=
  {| obj := ThreeObj
   ; hom := ThreeHom
   ; homset := Morphism_equality
   ; id := λ x, match x with
                | ThreeA => ThreeIdA
                | ThreeB => ThreeIdB
                | ThreeC => ThreeIdC
                end
  |}.
Next Obligation. three_solver. Defined.
Next Obligation. three_solver. Qed.
Next Obligation. three_solver. Qed.
Next Obligation. three_solver. Qed.
Next Obligation. three_solver. Qed.

Notation "3" := _3 : category_scope.