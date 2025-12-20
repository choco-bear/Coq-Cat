From Coq Require Export PeanoNat ZArith Lia.
Require Import Category.Lib.

Class IsCyclic (G : Group) :=
  { generator : G
  ; is_cyclic : ∀ g, ∃ n, g ≡ (generator^n)%group
  }.

Program Definition mk_cyclic_group n : Group :=
  {|  grp_carrier := Z
    ; grp_setoid := Z_mod_setoid n
    ; grp_op := {| op := Z.add |}
    ; grp_id := 0%Z
    ; grp_inv := λ x, (-x)%Z
  |}.
Next Obligation.
  proper. replace (_ - _)%Z with ((x - y) + (x0 - y0))%Z;
  now try apply divide_add; try nia. 
Qed.
Next Obligation. rewrite Z.sub_diag. apply divide_0_r. Qed.
Next Obligation. replace (_ - _)%Z with 0%Z by nia. apply divide_0_r. Qed.
Next Obligation. replace (_ - _)%Z with 0%Z by nia. apply divide_0_r. Qed.
Next Obligation. replace (_ - _)%Z with 0%Z by nia. apply divide_0_r. Qed.
Next Obligation. replace (_ - _)%Z with 0%Z by nia. apply divide_0_r. Qed.

#[export]
Program Instance cyclic_group_is_cyclic n
  : IsCyclic (mk_cyclic_group n) := {| generator := 1 |}%Z.
Next Obligation.
  exists g. assert ((1%Z : mk_cyclic_group n) ^ g = g)%group; cycle 1.
  { rewrite H, Z.sub_diag. apply divide_0_r. }
  destruct g; ss.
  - replace (Z.pos p) with (Z.pos p + 0)%Z by lia.
    remember 0%Z as m; clear Heqm; revert m.
    induction p; intro; try done.
    + replace (p~1)%positive with (1 + p + p)%positive by lia.
      rewrite !Pos.iter_add, !IHp, !Pos2Z.inj_add; unfold Pos.iter; lia.
    + replace (p~0)%positive with (p + p)%positive by lia.
      rewrite Pos.iter_add, !IHp, !Pos2Z.inj_add; lia.
  - replace (Z.neg p) with (Z.neg p + 0)%Z by lia.
    remember 0%Z as m; clear Heqm; revert m.
    induction p; intro; try done.
    + replace (p~1)%positive with (1 + p + p)%positive by lia.
      rewrite !Pos.iter_add, !IHp, <-!Pos2Z.add_neg_neg; unfold Pos.iter; lia.
    + replace (p~0)%positive with (p + p)%positive by lia.
      rewrite Pos.iter_add, !IHp, <-!Pos2Z.add_neg_neg; lia.
Qed.