Require Import Common.

Module Zero.
  Inductive Object := .

  Inductive Arrow : Object → Object → Type := .

  Ltac solver :=
    common_simpl;
    match goal with
    | [x : Object |- _] => depdes x
    | [f : Arrow _ _ |- _] => depdes f
    end.
  Local Obligation Tactic := solver.
  
  Definition comp {x y z} (f : Arrow y z) (g : Arrow x y) : Arrow x z.
  Proof. solver. Defined.

  Definition id x : Arrow x x.
  Proof. solver. Defined.
  
  Program Instance t : Category Object :=
    {|
      Category.Arrow := Arrow;
      Category.comp := @comp;
      cat_id := Zero.id;
    |}.

  Program Instance is_descrete : IsDiscrete t.

  Program Instance is_groupoid : IsGroupoid t.
End Zero.
Notation "0" := Zero.t : category_scope.

Module One.
  Inductive Object := A.
  
  Inductive Arrow : Object → Object → Type := id_A : Arrow A A.

  Ltac solver :=
    program_simpl; common_simpl;
    hrepeat progress do 1 match goal with
    | [x : Object |- _] => depdes x
    | [f : Arrow _ _ |- _] => depdes f
    end; ss.
  Local Obligation Tactic := repeat unshelve esplit; solver.

  Definition comp {x y z} (f : Arrow y z) (g : Arrow x y) : Arrow x z.
  Proof. solver. Defined.

  Definition id x : Arrow x x.
  Proof. solver. Defined.

  Program Instance t : Category Object :=
    {|
      Category.Arrow := Arrow;
      Category.comp := @comp;
      cat_id := One.id;
    |}.

  Program Instance is_descrete : IsDiscrete t.

  Program Instance is_group : IsGroup t.
End One.
Notation "1" := One.t : category_scope.

Module Two.
  Inductive Object := A | B.

  Inductive Arrow : Object → Object → Type :=
    | id_A : Arrow A A
    | id_B : Arrow B B
    | f_AB : Arrow A B
    .

  Ltac two_simpl :=
    hrepeat do 1 match goal with
    | [x : Object |- _] => depdes x
    | [f : Arrow _ _ |- _] => depdes f
    end; ss.

  Ltac solver := common_simpl; two_simpl; (hrepeat do 1 constructor); common_simpl.
  Local Obligation Tactic := solver.

  Definition comp {x y z} (f : Arrow y z) (g : Arrow x y) : Arrow x z.
  Proof. solver. Defined.

  Definition id x : Arrow x x.
  Proof. solver. Defined.

  Program Instance t : Category Object :=
    {|
      Category.Arrow := Arrow;
      Category.comp := @comp;
      cat_id := Two.id;
    |}.
End Two.
Notation "2" := Two.t : category_scope.

Module Three.
  Inductive Object := A | B | C.

  Inductive Arrow : Object → Object → Type :=
    | id_A : Arrow A A
    | id_B : Arrow B B
    | id_C : Arrow C C 
    | f_AB : Arrow A B
    | f_AC : Arrow A C
    | f_BC : Arrow B C
    .

  Ltac three_simpl :=
    hrepeat do 1 match goal with
    | [x : Object |- _] => depdes x
    | [f : Arrow _ _ |- _] => depdes f
    end; ss.

  Ltac solver := common_simpl; three_simpl; (hrepeat do 1 constructor); common_simpl.
  Local Obligation Tactic := solver.

  Definition comp {x y z} (f : Arrow y z) (g : Arrow x y) : Arrow x z.
  Proof. solver. Defined.

  Definition id x : Arrow x x.
  Proof. solver. Defined.

  Program Instance t : Category Object :=
    {|
      Category.Arrow := Arrow;
      Category.comp := @comp;
      cat_id := Three.id;
    |}.
End Three.
Notation "3" := Three.t : category_scope.

Module Parallel.
  Inductive Object := A | B.

  Inductive Arrow : Object → Object → Type :=
    | id_A : Arrow A A
    | id_B : Arrow B B
    | f_AB : Arrow A B 
    | g_AB : Arrow A B
    .

  Ltac par_simpl :=
    hrepeat do 1 match goal with
    | [x : Object |- _] => depdes x
    | [f : Arrow _ _ |- _] => depdes f
    end; ss.
    
  Ltac solver := common_simpl; par_simpl; (hrepeat do 1 constructor); common_simpl.
  Local Obligation Tactic := solver.

  Definition comp {x y z} (f : Arrow y z) (g : Arrow x y) : Arrow x z.
  Proof. par_simpl. Defined.

  Definition id x : Arrow x x.
  Proof. solver. Defined.

  Program Instance t : Category Object := 
    {|
      Category.Arrow := Arrow;
      Category.comp := @comp;
      cat_id := Parallel.id;
    |}.
End Parallel.
Notation "⇊" := Parallel.t : category_scope.

Module Discrete. Section Defs.
  Context (Object : Type).

  Inductive Arrow : Object → Object → Type :=
    | id x : Arrow x x
    .

  Ltac solver :=
    program_simpl; common_simpl;
    hrepeat do 1 match goal with
    | [f : Arrow _ _ |- _] => depdes f
    end; ss.
  Local Obligation Tactic := solver.

  Definition comp {x y z} (f : Arrow y z) (g : Arrow x y) : Arrow x z.
  Proof. solver. Defined.

  Program Instance from_type : Category Object :=
    {|
      Category.Arrow := Arrow;
      Category.comp := @comp;
      cat_id := Defs.id;
    |}.

  Program Instance is_descrete : IsDiscrete from_type.
End Defs. End Discrete.