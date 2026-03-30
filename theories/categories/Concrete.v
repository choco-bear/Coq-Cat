(* From mathcomp Require Import ssreflect all_algebra. *)
Require Import Common Sets.

Module Mon.
  Structure Object := {
    obj : Type;
    monoid : Category obj;
    is_monoid :: IsMonoid monoid;
  }.

  Local Notation MonArrow := (λ M M' : Object, monoid M ⟶ monoid M').

  Program Instance t : Category Object :=
    {|
      Arrow   := MonArrow;
      comp    := λ M1 M2 M3 ϕ ψ, ϕ ∘ ψ;
      cat_id  := λ M, id[monoid M];
    |}%functor.
  Solve Obligations with functor_solver.

  Program Definition Forgetful : t ⟶ Sets.t :=
    {|
      fobj := λ M, obj[monoid M];
      fmap := λ M1 M2 ϕ, fobj ϕ;
    |}.
End Mon.
Existing Instance Mon.t.
Existing Instance is_monoid.
Coercion Mon.monoid : Mon.Object >-> Category.

Module Grp.
  Structure Object := {
    obj : Type;
    group : Category obj;
    is_group :: IsGroup group;
  }.

  Local Notation GrpArrow := (λ G G' : Object, group G ⟶ group G').
  
  Program Instance t : Category Object :=
    {|
      Arrow   := GrpArrow;
      comp    := λ G H K ϕ ψ, ϕ ∘ ψ;
      cat_id  := λ G, id[group G];
    |}%functor.
  Solve Obligations with functor_solver.

  Program Definition Forgetful : t ⟶ Sets.t :=
    {|
      fobj := λ G, obj[group G];
      fmap := λ G H ϕ, fobj ϕ;
    |}.

  Definition grp2mon (G : Object) : Mon.Object :=
    {|
      Mon.obj := obj[group G];
      Mon.monoid := group G;
    |}.

  Program Definition BinaryProduct (G H : Object) : Object := {| group := group G × group H |}.
  Next Obligation. cby construct. Qed.
End Grp.
Existing Instance Grp.t.
Existing Instance Grp.is_group.
Coercion Grp.group : Grp.Object >-> Category.
Coercion Grp.grp2mon : Grp.Object >-> Mon.Object.

Module GrpNotations.
  Declare Scope grp_scope.
  Delimit Scope grp_scope with grp.
  Bind Scope grp_scope with Grp.Object.

  Notation "G × H" := (BinaryProduct G%grp H%grp) : grp_scope.
End GrpNotations.