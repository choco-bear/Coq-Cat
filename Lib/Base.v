From Coq Require Export Program.
From Coq Require Export CMorphisms.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Close Scope nat_scope.

Declare Scope category_theory_scope.
Delimit Scope category_theory_scope with category_theory.
Open Scope category_theory_scope.

Notation "`` x" := (@projT1 _ _ x) (at level 0) : category_theory_scope.
Notation "( x ; y )" := (existT _ x y) (at level 0) : category_theory_scope.

Notation "`1 x" := (@projT1 _ _ x) (at level 0) : category_theory_scope.
Notation "`2 x" := (@projT2 _ _ x) (at level 0) : category_theory_scope.
Notation "`3 x" := (@projT3 _ _ x) (at level 0) : category_theory_scope.

Tactic Notation "given" "(" ident(H) ":" lconstr(type) ")" tactic(t) :=
  unshelve (refine (let H := (_ : type) in _)); [..|t].

Tactic Notation "given" "(" ident(H) ":" lconstr(type) ")" :=
 given (H : type) idtac.

Tactic Notation "sufficient" lconstr(type) "by" tactic(t) :=
  let GOAL := fresh "GOAL" in given (GOAL : type) (solve [t]).

Tactic Notation "sufficient" lconstr(type) :=
  sufficient type by (solve [intuition|auto|eauto]).

#[export] Hint Unfold Basics.compose : core.
#[export] Hint Unfold Basics.arrow : core.
#[export] Hint Unfold Datatypes.id : core.
#[export] Hint Constructors sigT : core.

Arguments Basics.compose {_ _ _} _ _ /.
Arguments Basics.arrow _ _ /.
Arguments Datatypes.id {_} _ /.

Inductive poly_unit : Type := ttt.
#[export] Hint Constructors poly_unit : core.

Inductive poly_void : Type := .

Definition notT (X : Type) := X -> poly_void.
#[export] Hint Unfold notT : core.

Notation "∀  x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 10, x binder, y binder, P at level 200, right associativity) :
  category_theory_scope.

Notation "'exists' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'") :
  category_theory_scope.
Notation "∃  x .. y , P" := (exists x, .. (exists y, P) ..)
  (at level 10, x binder, y binder, P at level 200, right associativity) :
  category_theory_scope.
#[export] Hint Constructors sigT : core.

Global Instance proper_sigT A
  : Proper ((pointwise_relation A iffT) ==> iffT) (@sigT A).
Proof. intros P Q H; split; intros []; eexists; apply H; eauto. Qed.

Notation "x → y" := (x -> y)
  (at level 99, y at level 200, right associativity): category_theory_scope.
Notation "x ↔ y" := (iffT x y)
  (at level 95, no associativity) : category_theory_scope.
Notation "¬ x" := (notT x)
  (at level 75, right associativity) : category_theory_scope.
Notation "x ≠ y" := (¬ (x = y)) (at level 70) : category_theory_scope.

Infix "∧" := prod (at level 80, right associativity) : category_theory_scope.
Infix "∨" := sum (at level 85, right associativity) : category_theory_scope.
#[export] Hint Constructors prod sum : core.

Global Instance proper_prod
  : Proper (iffT ==> iffT ==> iffT) prod.
Proof. intros X1 Y1 [] X2 Y2 []; split; intuition. Qed.

Global Instance proper_sum
  : Proper (iffT ==> iffT ==> iffT) sum.
Proof. intros X1 Y1 [] X2 Y2 []; split; intuition. Qed.

Global Instance proper_notT
  : Proper (iffT ==> iffT) notT.
Proof. intros X Y []; split; intuition. Qed.

Notation "'λ'  x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 10, x binder, y binder, t at level 200, right associativity) :
  category_theory_scope.