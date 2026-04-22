From CoqCat Require Import Common Product.

Create HintDb __Sets discriminated.
Module Sets.
  Structure Object := from_type { _set : Type }.

  Inductive Arrow X Y := from_ftn (ftn : _set X → _set Y).
  #[export] Hint Constructors Arrow : coqcat __Sets.

  Definition apply {X Y} (f : Arrow X Y) (x : _set X) : _set Y.
  Proof. depdes f. apply ftn, x. Defined.

  Definition comp {x y z} (f : Arrow y z) (g : Arrow x y) : Arrow x z.
  Proof. depdes f g. apply from_ftn. i. apply ftn, ftn0, X. Defined.

  #[export] Hint Unfold apply comp : __Sets.

  Lemma Arrow_ext X Y (f g : _set X → _set Y)
    : f = g
    → from_ftn X Y f = from_ftn X Y g.
  Proof. common_simpl. Qed.

  Lemma equal_f X Y (f g : Arrow X Y) (x : _set X)
    : f = g
    → apply f x = apply g x.
  Proof. common_simpl. Qed.
  
  #[export] Hint Resolve Arrow_ext func_ext equal_f : __Sets.

  Ltac simpl := repeat first [ fail
                | match goal with
                  | H : Arrow _ _ |- _ => depdes H
                  | _ => apply Arrow_ext
                  | _ => apply func_ext
                  end; ss
                | ii ].

  Ltac solver := cby (program_simpl; common_simpl; Sets.simpl).
  
  Program Instance t : Category Object :=
    {|
      Category.Arrow := Arrow;
      Category.comp := @comp;
      cat_id := λ X, from_ftn X X (λ x, x);
    |}.
  Solve Obligations with solver.

  Program Definition BinaryProduct : t × t ⟶ t :=
    {|
      fobj := λ XY, from_type (_set XY.1 * _set XY.2);
      fmap := λ _ _ fg, from_ftn _ _ (λ xy, (apply fg.1 xy.1, apply fg.2 xy.2));
    |}.
  Solve Obligations with solver.
End Sets.
Existing Instance Sets.t.
Arguments Sets.from_ftn {X Y} ftn%_function_scope.
Coercion Sets._set : Sets.Object >-> Sortclass.
Coercion Sets.from_type : Sortclass >-> Sets.Object.
Coercion Sets.apply : Sets.Arrow >-> Funclass.

Lemma Sets_id_unfold X x : id{Sets.t}[X]%morphism x = x.
Proof. Sets.solver. Qed.
Lemma Sets_comp_unfold [X Y Z : Sets.Object] (f : Y ~> Z) (g : X ~> Y) x : (f ∘ g)%morphism x = f (g x).
Proof. Sets.solver. Qed.
#[export] Hint Rewrite @Sets_id_unfold @Sets_comp_unfold : normalize.

Program Definition Powerset : Sets.t ⟶ Sets.t :=
  {|
    fobj := λ X, X → Prop;
    fmap := λ X Y f, Sets.from_ftn (λ P y, ∃ x, P x ∧ y = f x);
  |}.
Next Obligation.
  Sets.simpl. apply prop_ext.
  cby split=> [[?] [/[swap] ->]|].
Qed.
Next Obligation.
  Sets.simpl. apply prop_ext.
  cby split=> [[?] [/[swap] ->]|[?] [[?] /[swap] ->] [/[swap] ->]].
Qed.

Program Instance SetsIsKaroubiClosed : IsKaroubiClosed Sets.t.
Next Obligation.
  unshelve eapply (mk_SplitIdempotent (f : x ~{Sets.t}~> x) {a : x & ∃ b, a = f b} ).
  { construct. unshelve esplit; first exact (f X); eauto. }
  { Sets.simpl. construct. depdes X. exact x0. }
  all: Sets.simpl.
  depdes x0. des. subst. apply subsetT_eq_compat.
  depdes Idempotent0. cby eapply Sets.equal_f in idempotent.
Qed.

Module PtSets.
  Structure Object := from_pt {
    _set : Type;
    pt : _set;
  }.

  Inductive Arrow x y := from_ftn (ftn : _set x → _set y) (pt_compat : ftn (pt x) = pt y).

  Definition comp {x y z} (f : Arrow y z) (g : Arrow x y) : Arrow x z.
  Proof.
    depdes f g; unshelve esplit.
    - exact (ftn ∘ ftn0).
    - s. rewrite pt_compat0 pt_compat //.
  Defined.

  Lemma Arrow_ext x y ftn1 ftn2 pt_compat1 pt_compat2
    :  ftn1 = ftn2
    → from_ftn x y ftn1 pt_compat1 = from_ftn x y ftn2 pt_compat2.
  Proof. cby common_simpl; assert (pt_compat1 = pt_compat2). Qed.

  Ltac solver := by program_simpl; common_simpl; repeat match goal with H : Arrow _ _ |- _ => depdes H end; ss; apply Arrow_ext.
  
  Program Instance t : Category Object :=
    {|
      Category.Arrow := Arrow;
      Category.comp := @comp;
      cat_id := λ x, from_ftn x x (λ x, x) _
    |}.
  Solve Obligations with solver.
End PtSets.
Existing Instance PtSets.t.
Coercion PtSets._set : PtSets.Object >-> Sortclass.
Arguments PtSets.from_pt {_set}%_type_scope pt.

Module SetsNotations.
  Declare Scope sets_scope.
  Delimit Scope sets_scope with sets.
  Bind Scope sets_scope with Sets.Object.

  Notation "X × Y" := (Sets.from_type (Sets._set X%sets * Sets._set Y%sets)%type) : sets_scope.
  Notation "X + Y" := (Sets.from_type (Sets._set X%sets + Sets._set Y%sets)%type) : sets_scope.
  Notation "X → Y" := (Sets.from_type (Sets._set X%sets → Sets._set Y%sets)%type) : sets_scope.
  Notation "'𝒫'" := Powerset (at level 0) : sets_scope.
  Notation "'(-×-)'" := Sets.BinaryProduct (at level 0) : sets_scope.
End SetsNotations.