From Coq Require Import PeanoNat ZArith Lia.
Require Export Category.Lib.List.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Local Open Scope nat_scope.
Local Open Scope Z_scope.

Definition divide (x y : Z) : Type := ∃ z, y = z * x.

Notation "( x | y )" := (divide x%Z y%Z) : Z_scope.

Program Definition nat_setoid : Setoid nat := eq_Setoid nat.

Program Definition Z_setoid : Setoid Z := eq_Setoid Z.

Program Definition Z_mod_setoid z : Setoid Z :=
  {| equiv := λ x y, (z | x - y) |}.
Next Obligation.
  split; repeat intro.
  - exists 0; nia.
  - destruct H as [n ?]; exists (-n); nia.
  - destruct H as [n ?], H0 as [m ?]; exists (n + m); nia.
Qed.

Lemma divide_refl n : (n | n).
Proof. exists 1; nia. Qed.
Lemma divide_trans n m p : (n | m) → (m | p) → (n | p).
Proof. intros [x ?] [y ?]. exists (x * y); nia. Qed.
Lemma divide_0_r n : (n | 0).
Proof. now exists 0. Qed.
Lemma divide_1_l n : (1 | n).
Proof. exists n; nia. Qed.
Lemma divide_add n m p : (n | m) → (n | p) → (n | m + p).
Proof. intros [x ?] [y ?]. exists (x + y); nia. Qed.

#[export] Program Instance divide_preorder : PreOrder divide.
Next Obligation. exists 1; nia. Qed.
Next Obligation. intros x y z [n ?] [m ?]. exists (n * m); nia. Qed.