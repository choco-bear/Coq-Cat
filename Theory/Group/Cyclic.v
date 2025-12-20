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