From mathcomp Require Import ssreflect all_algebra.
Require Import Common Sets.

Module Mon.
  Structure Object := {
    obj : Type;
    #[export] monoid :> Category obj;
    #[export] is_group :: IsMonoid monoid;
  }.

  Local Notation MonArrow := (λ M M' : Object, M ⟶ M').

  Program Definition Mon : Category Object :=
    {|
      Arrow   := MonArrow;
      comp    := λ M1 M2 M3 ϕ ψ, ϕ ∘ ψ;
      cat_id  := λ M, Id[M];
    |}%functor.
  Solve Obligations with functor_solver.

  Program Definition Forgetful : Mon ⟶ Sets :=
    {|
      fobj := λ M, obj[M];
      fmap := λ M1 M2 ϕ, fobj ϕ;
    |}.
End Mon.

Module Grp.
  Structure Object := {
    obj : Type;
    #[export] group :> Category obj;
    #[export] is_group :: IsGroup group;
  }.

  Local Notation GrpArrow := (λ G G' : Object, G ⟶ G').
  
  Program Definition Grp : Category Object :=
    {|
      Arrow   := GrpArrow;
      comp    := λ G H K ϕ ψ, ϕ ∘ ψ;
      cat_id  := λ G, Id[G];
    |}%functor.
  Solve Obligations with functor_solver.

  Program Definition Forgetful : Grp ⟶ Sets :=
    {|
      fobj := λ G, obj[G];
      fmap := λ G H ϕ, fobj ϕ;
    |}.

  Definition grp2mon (G : Object) : Mon.Object :=
    {|
      Mon.obj := obj[G];
      Mon.monoid := G;
    |}.
End Grp.
#[export] Coercion Grp.grp2mon : Grp.Object >-> Mon.Object.