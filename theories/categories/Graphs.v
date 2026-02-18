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
  
  Program Instance Zero : Category Object :=
    {|
      Category.Arrow := Arrow;
      Category.comp := @comp;
      cat_id := Zero.id;
    |}.
End Zero.
Notation "0" := Zero.Zero : category_scope.

Module One.
  Inductive Object := A.
  
  Inductive Arrow : Object → Object → Type := id_A : Arrow A A.

  Ltac solver :=
    common_simpl;
    hrepeat progress do 1 match goal with
    | [x : Object |- _] => depdes x
    | [f : Arrow _ _ |- _] => depdes f
    end; ss.
  Local Obligation Tactic := solver.

  Definition comp {x y z} (f : Arrow y z) (g : Arrow x y) : Arrow x z.
  Proof. solver. Defined.

  Definition id x : Arrow x x.
  Proof. solver. Defined.

  Program Instance One : Category Object :=
    {|
      Category.Arrow := Arrow;
      Category.comp := @comp;
      cat_id := One.id;
    |}.
End One.
Notation "1" := One.One : category_scope.

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

  Ltac solver := common_simpl; two_simpl; hrepeat do 1 constructor.
  Local Obligation Tactic := solver.

  Definition comp {x y z} (f : Arrow y z) (g : Arrow x y) : Arrow x z.
  Proof. solver. Defined.

  Definition id x : Arrow x x.
  Proof. solver. Defined.

  Program Instance Two : Category Object :=
    {|
      Category.Arrow := Arrow;
      Category.comp := @comp;
      cat_id := Two.id;
    |}.
End Two.
Notation "2" := Two.Two : category_scope.

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

  Ltac solver := common_simpl; three_simpl; hrepeat do 1 constructor.
  Local Obligation Tactic := solver.

  Definition comp {x y z} (f : Arrow y z) (g : Arrow x y) : Arrow x z.
  Proof. solver. Defined.

  Definition id x : Arrow x x.
  Proof. solver. Defined.

  Program Instance Three : Category Object :=
    {|
      Category.Arrow := Arrow;
      Category.comp := @comp;
      cat_id := Three.id;
    |}.
End Three.
Notation "3" := Three.Three : category_scope.

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
    
  Ltac solver := common_simpl; par_simpl; hrepeat do 1 constructor.
  Local Obligation Tactic := solver.

  Definition comp {x y z} (f : Arrow y z) (g : Arrow x y) : Arrow x z.
  Proof. par_simpl. Defined.

  Definition id x : Arrow x x.
  Proof. solver. Defined.

  Program Instance Parallel : Category Object := 
    {|
      Category.Arrow := Arrow;
      Category.comp := @comp;
      cat_id := Parallel.id;
    |}.
End Parallel.
Notation "⇊" := Parallel.Parallel : category_scope.