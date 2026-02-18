From mathcomp Require Import ssreflect all_algebra.
Require Import Common Sets.

Module Mon.
  Structure Object := {
    obj : Type;
    monoid : Category obj;
    #[export] is_monoid :: IsMonoid monoid;
  }.

  Local Notation MonArrow := (λ M M' : Object, monoid M ⟶ monoid M').

  Program Instance Mon : Category Object :=
    {|
      Arrow   := MonArrow;
      comp    := λ M1 M2 M3 ϕ ψ, ϕ ∘ ψ;
      cat_id  := λ M, Id[monoid M];
    |}%functor.
  Solve Obligations with functor_solver.

  Program Definition Forgetful : Mon ⟶ Sets :=
    {|
      fobj := λ M, obj[monoid M];
      fmap := λ M1 M2 ϕ, fobj ϕ;
    |}.
End Mon.
Coercion Mon.monoid : Mon.Object >-> Category.

Module Grp.
  Structure Object := {
    obj : Type;
    group : Category obj;
    #[export] is_group :: IsGroup group;
  }.

  Local Notation GrpArrow := (λ G G' : Object, group G ⟶ group G').
  
  Program Instance Grp : Category Object :=
    {|
      Arrow   := GrpArrow;
      comp    := λ G H K ϕ ψ, ϕ ∘ ψ;
      cat_id  := λ G, Id[group G];
    |}%functor.
  Solve Obligations with functor_solver.

  Program Definition Forgetful : Grp ⟶ Sets :=
    {|
      fobj := λ G, obj[group G];
      fmap := λ G H ϕ, fobj ϕ;
    |}.

  Definition grp2mon (G : Object) : Mon.Object :=
    {|
      Mon.obj := obj[group G];
      Mon.monoid := group G;
    |}.
End Grp.
Coercion Grp.group : Grp.Object >-> Category.
Coercion Grp.grp2mon : Grp.Object >-> Mon.Object.