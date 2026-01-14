Require Export Category.Lib.Setoid.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Open Scope lazy_bool_scope.

Lemma pair_injection [A B : Type] (a1 a2 : A) (b1 b2 : B)
  : (a1, b1) = (a2, b2) → a1 = a2 ∧ b1 = b2.
Proof. inversion 1; eauto. Qed.

(** Basic tactics for category theory proofs *)
Ltac simplify :=
  simpl in *; repeat
    (match goal with
     | [ H : () |- _ ] => destruct H
     | [ |- () ] => exact tt

     | [ H : poly_unit |- _ ] => destruct H
     | [ |- poly_unit ] => exact ttt

     | [ H : _ ∧ _ |- _ ] =>
       let H' := fresh "H" in destruct H as [H H']
     | [ |- _ ∧ _ ] => split

     | [ H : _ /\ _ |- _ ] =>
       let H' := fresh "H" in destruct H as [H H']
     | [ |- _ /\ _ ] => split

     | [ H : _ ↔ _ |- _ ] =>
       let H' := fresh "H" in destruct H as [H H']
     | [ |- _ ↔ _ ] => split

     | [ H : (_, _) = (_, _) |- _ ] =>
       first [ apply pair_injection in H
             | inversion H; subst; assert (H = eq_refl) as -> by apply proof_irrelevance ]

     | [ H : _ * _ |- _ ] =>
       let x := fresh "x" in
       let y := fresh "y" in
       destruct H as [x y]
     | [ |- _ * _ ] => split

     | [ H : { _ : _ & _ } |- _ ] =>
       let x := fresh "x" in
       let e := fresh "e" in
       destruct H as [x e]
     | [ |- { _ : _ & _ } ] =>
       unshelve (refine (existT _ _ _))

     | [ |- context[eq_rect_r] ] => unfold eq_rect_r, eq_rect, eq_sym, eq_trans
     | [ |- context[eq_rect] ] => unfold eq_rect, eq_sym, eq_trans
     end; repeat intro); subst.


(** [repeat] guranteeing termination *)
Tactic Notation "hrepeat_or_fail" tactic(tac) :=
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
  tryif tac then (
      fail 10
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else idtac
  ) else fail
.
Tactic Notation "hrepeat" tactic(tac) := try (hrepeat_or_fail tac).

(** Short for common tactics *)
Tactic Notation "econs" := econstructor.
Tactic Notation "econs" int_or_var(x) := econstructor x.
Tactic Notation "i" := intros.
Tactic Notation "ii" := hrepeat do 1 intro.
Tactic Notation "s" := simpl.
Tactic Notation "s" ident(a) := simpl a.
Tactic Notation "s" constr(t) := simpl t.
Tactic Notation "s" "in" hyp(H) := simpl in H.
Tactic Notation "ss" := ii; simpl in *; try now idtac.
Tactic Notation "r" := red.
Tactic Notation "r" "in" hyp(H) := red in H.
Tactic Notation "rr" := hrepeat do 1 red.
Tactic Notation "rr" "in" hyp(H) := hrepeat do 1 red in H.

(** [cat] tactic is like [set_solver] in coq-stdpp. But much weaker and faster. *)
Ltac cat :=
  simplify;
  autorewrite with categories in *;
  auto with category_laws;
  try reflexivity.

Tactic Notation "by" tactic(t) := solve [t; cat].

(** Hints for dealing with equivalences *)
#[export] Hint Constructors Equivalence : core.

#[export] Hint Unfold Reflexive : core.
#[export] Hint Unfold Symmetric : core.
#[export] Hint Unfold Transitive : core.

#[export] Hint Extern 1 (Reflexive ?X) =>
  unfold Reflexive : core.
#[export] Hint Extern 1 (Symmetric ?X) =>
  unfold Symmetric : core.
#[export] Hint Extern 1 (Transitive ?X) =>
  unfold Transitive : core.
#[export] Hint Extern 1 (Equivalence ?X) =>
  apply Build_Equivalence : core.
#[export] Hint Extern 1 (Proper _ _) => unfold Proper : core.
#[export] Hint Extern 8 (respectful _ _ _ _) =>
  unfold respectful : core.

#[export] Hint Extern 4 (equiv ?A ?A) => reflexivity : category_laws.
#[export] Hint Extern 6 (equiv ?X ?Y) =>
  apply Equivalence_Symmetric : category_laws.
#[export] Hint Extern 7 (equiv ?X ?Z) =>
  match goal with
    [H : equiv ?X ?Y, H' : equiv ?Y ?Z |- equiv ?X ?Z] => transitivity Y
  end : category_laws.

(** Useful when dealing with [Equivalence] instances. *)
Ltac equivalence :=
  constructor; repeat intro; simpl; try cat; intuition; auto with *.

(** Useful when dealing with [Proper] instances. *)
Ltac proper := repeat intro; simpl; try cat; intuition.

(** Useful when dealing with [Property] instances. *)
Ltac property := constructor; repeat intro; simpl; try cat intuition.

(** Normalize the categorical expressions *)
Tactic Notation "normalize" := autorewrite with normalize.
Tactic Notation "normalize" "in" hyp(H) := autorewrite with normalize in H.

(** Rewrite using a term, simplifying it first. *)
Tactic Notation "srewrite" uconstr(F) :=
  let H := fresh "H" in pose proof F as H; cbn in H; rewrite H; clear H.
Tactic Notation "srewrite" "->" uconstr(F) :=
  let H := fresh "H" in pose proof F as H; cbn in H; rewrite -> H; clear H.
Tactic Notation "srewrite" "<-" uconstr(F) :=
  let H := fresh "H" in pose proof F as H; cbn in H; rewrite <- H; clear H.

Tactic Notation "srewrite" uconstr(F) "in" hyp(H) :=
  let H' := fresh "H" in pose proof F as H'; cbn in H'; rewrite H' in H; clear H'.
Tactic Notation "srewrite" "->" uconstr(F) "in" hyp(H) :=
  let H' := fresh "H" in pose proof F as H'; cbn in H'; rewrite -> H' in H; clear H'.
Tactic Notation "srewrite" "<-" uconstr(F) "in" hyp(H) :=
  let H' := fresh "H" in pose proof F as H'; cbn in H'; rewrite <- H' in H; clear H'.

Tactic Notation "srewrite" uconstr(F) "in" "*" :=
  let H := fresh "H" in pose proof F as H; cbn in H; rewrite H in *; clear H.
Tactic Notation "srewrite" "->" uconstr(F) "in" "*" :=
  let H := fresh "H" in pose proof F as H; cbn in H; rewrite -> H in *; clear H.
Tactic Notation "srewrite" "<-" uconstr(F) "in" "*" :=
  let H := fresh "H" in pose proof F as H; cbn in H; rewrite <- H in *; clear H.

(** The setoid version of the tactic [subst] *)
Ltac rewrites :=
  repeat match goal with
  | [ H : ?X ≡ ?Y                      |- context[?X] ] => rewrite !H; clear H
  | [ H : ?X ≡ ?Y                      |- context[?X] ] => srewrite H; clear H
  | [ H : ∀ _, ?X ≡ ?Y                 |- context[?X] ] => rewrite !H; clear H
  | [ H : ∀ _, ?X ≡ ?Y                 |- context[?X] ] => srewrite H; clear H
  | [ H : ∀ _, ?X _ ≡ ?Y _             |- context[?X] ] => rewrite !H; clear H
  | [ H : ∀ _, ?X _ ≡ ?Y _             |- context[?X] ] => srewrite H; clear H
  | [ H : ∀ _ _, ?X ≡ ?Y               |- context[?X] ] => rewrite !H; clear H
  | [ H : ∀ _ _, ?X ≡ ?Y               |- context[?X] ] => srewrite H; clear H
  | [ H : ∀ _ _, ?X _ ≡ ?Y _           |- context[?X] ] => rewrite !H; clear H
  | [ H : ∀ _ _, ?X _ ≡ ?Y _           |- context[?X] ] => srewrite H; clear H
  | [ H : ∀ _ _, ?X _ _ ≡ ?Y _ _       |- context[?X] ] => rewrite !H; clear H
  | [ H : ∀ _ _, ?X _ _ ≡ ?Y _ _       |- context[?X] ] => srewrite H; clear H
  | [ H : ∀ _ _ _, ?X ≡ ?Y             |- context[?X] ] => rewrite !H; clear H
  | [ H : ∀ _ _ _, ?X ≡ ?Y             |- context[?X] ] => srewrite H; clear H
  | [ H : ∀ _ _ _, ?X _ ≡ ?Y _         |- context[?X] ] => rewrite !H; clear H
  | [ H : ∀ _ _ _, ?X _ ≡ ?Y _         |- context[?X] ] => srewrite H; clear H
  | [ H : ∀ _ _ _, ?X _ _ ≡ ?Y _ _     |- context[?X] ] => rewrite !H; clear H
  | [ H : ∀ _ _ _, ?X _ _ ≡ ?Y _ _     |- context[?X] ] => srewrite H; clear H
  | [ H : ∀ _ _ _, ?X _ _ _ ≡ ?Y _ _ _ |- context[?X] ] => rewrite !H; clear H
  | [ H : ∀ _ _ _, ?X _ _ _ ≡ ?Y _ _ _ |- context[?X] ] => srewrite H; clear H

  | [ H : ?X ≡ ?Y                      |- context[?Y] ] => rewrite <- !H; clear H
  | [ H : ?X ≡ ?Y                      |- context[?Y] ] => srewrite <- H; clear H
  | [ H : ∀ _, ?X ≡ ?Y                 |- context[?Y] ] => rewrite <- !H; clear H
  | [ H : ∀ _, ?X ≡ ?Y                 |- context[?Y] ] => srewrite <- H; clear H
  | [ H : ∀ _, ?X _ ≡ ?Y _             |- context[?Y] ] => rewrite <- !H; clear H
  | [ H : ∀ _, ?X _ ≡ ?Y _             |- context[?Y] ] => srewrite <- H; clear H
  | [ H : ∀ _ _, ?X ≡ ?Y               |- context[?Y] ] => rewrite <- !H; clear H
  | [ H : ∀ _ _, ?X ≡ ?Y               |- context[?Y] ] => srewrite <- H; clear H
  | [ H : ∀ _ _, ?X _ ≡ ?Y _           |- context[?Y] ] => rewrite <- !H; clear H
  | [ H : ∀ _ _, ?X _ ≡ ?Y _           |- context[?Y] ] => srewrite <- H; clear H
  | [ H : ∀ _ _, ?X _ _ ≡ ?Y _ _       |- context[?Y] ] => rewrite <- !H; clear H
  | [ H : ∀ _ _, ?X _ _ ≡ ?Y _ _       |- context[?Y] ] => srewrite <- H; clear H
  | [ H : ∀ _ _ _, ?X ≡ ?Y             |- context[?Y] ] => rewrite <- !H; clear H
  | [ H : ∀ _ _ _, ?X ≡ ?Y             |- context[?Y] ] => srewrite <- H; clear H
  | [ H : ∀ _ _ _, ?X _ ≡ ?Y _         |- context[?Y] ] => rewrite <- !H; clear H
  | [ H : ∀ _ _ _, ?X _ ≡ ?Y _         |- context[?Y] ] => srewrite <- H; clear H
  | [ H : ∀ _ _ _, ?X _ _ ≡ ?Y _ _     |- context[?Y] ] => rewrite <- !H; clear H
  | [ H : ∀ _ _ _, ?X _ _ ≡ ?Y _ _     |- context[?Y] ] => srewrite <- H; clear H
  | [ H : ∀ _ _ _, ?X _ _ _ ≡ ?Y _ _ _ |- context[?Y] ] => rewrite <- !H; clear H
  | [ H : ∀ _ _ _, ?X _ _ _ ≡ ?Y _ _ _ |- context[?Y] ] => srewrite <- H; clear H
  end.

(** Apply a term, simplifying it first. *)
Tactic Notation "sapply" uconstr(F) :=
  let H := fresh "H" in pose proof F as H; cbn in H; apply H; clear H.
Tactic Notation "sapply" uconstr(F) "in" hyp(H) :=
  let H' := fresh "H" in pose proof F as H'; cbn in H'; apply H' in H; clear H'.

(** Simplify obligations generated by Program mode in category theory proofs *)
Ltac cat_simpl :=
  program_simpl; autounfold;
  try solve [
    repeat match goal with
    | [ |- Equivalence _ ] => equivalence
    | [ |- Proper _ _ ] => proper
    | [ |- respectful _ _ _ _ ] => proper
    end;
    program_simpl; autounfold in *;
    simpl in *; intros; simplify;
    simpl in *; cat; try apply _;
    rewrites; try now normalize];
  simpl in *; try now idtac.
#[global] Obligation Tactic := cat_simpl.

(** General form of [equivalence] or of [proper]. *)
Ltac construct := unshelve econstructor; simpl; intros.

(** Inversion with [subst] and [clear]. *)
Ltac inv H := inversion H; subst; try clear H.

(** Pose proof and simplify it. *)
Tactic Notation "spose" uconstr(H) "as" ident(X) :=
  pose proof H as X; simpl in X.

(** Clear a hypothesis and also its dependencies. Taken from Coq stdlib, with the
  * performance-enhancing change to [lazymatch] suggested at
  * [https://github.com/coq/coq/issues/11689].
  *)
Tactic Notation "clear" "dependent" hyp(h) :=
  let rec depclear h :=
  clear h ||
  lazymatch goal with
   | H : context [ h ] |- _ => depclear H; depclear h
  end ||
  fail "hypothesis to clear is used in the conclusion (maybe indirectly)"
 in depclear h.

(** A version of [generalize dependent] that applies only to a hypothesis.
  * Taken from Coq stdlib.
  *)
Tactic Notation "revert" "dependent" hyp(h) :=
  generalize dependent h.

(** Applying a tactic to a term with increasingly many arguments *)
Tactic Notation "do_with_holes" tactic3(x) uconstr(p) :=
  x uconstr:(p) ||
  x uconstr:(p _) ||
  x uconstr:(p _ _) ||
  x uconstr:(p _ _ _) ||
  x uconstr:(p _ _ _ _) ||
  x uconstr:(p _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).

(** Same thing but starting with many holes first *)
Tactic Notation "do_with_holes'" tactic3(x) uconstr(p) :=
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _) ||
  x uconstr:(p _ _ _ _) ||
  x uconstr:(p _ _ _) ||
  x uconstr:(p _ _) ||
  x uconstr:(p _) ||
  x uconstr:(p).

(** A shorter name for [simple refine]. *)
Tactic Notation "srefine" uconstr(term) := simple refine term.
(** A shorter name for [notypeclasses refine];. *)
Tactic Notation "nrefine" uconstr(term) := notypeclasses refine term.
(** A shorter name for [simple notypeclasses refine]. *)
Tactic Notation "snrefine" uconstr(term) := simple notypeclasses refine term.

(** Note that the Coq standard library has a [rapply], but it is like our [rapply']
  * with many-holes first. We prefer fewer-holes first, for instance so that a
  * theorem producing an equivalence will by preference be used to produce an
  * equivalence rather than to apply the coercion of that equivalence to a function.
  *)
Tactic Notation "rapply" uconstr(term)
  := do_with_holes ltac:(fun x => refine x) term.
Tactic Notation "rapply'" uconstr(term)
  := do_with_holes' ltac:(fun x => refine x) term.

Tactic Notation "srapply" uconstr(term)
  := do_with_holes ltac:(fun x => srefine x) term.
Tactic Notation "srapply'" uconstr(term)
  := do_with_holes' ltac:(fun x => srefine x) term.

Tactic Notation "nrapply" uconstr(term)
  := do_with_holes ltac:(fun x => nrefine x) term.
Tactic Notation "nrapply'" uconstr(term)
  := do_with_holes' ltac:(fun x => nrefine x) term.

Tactic Notation "snrapply" uconstr(term)
  := do_with_holes ltac:(fun x => snrefine x) term.
Tactic Notation "snrapply'" uconstr(term)
  := do_with_holes' ltac:(fun x => snrefine x) term.

(** Very fast [done] tactic. *)
Ltac done := now idtac.
Tactic Notation "nby" tactic(t) := now (t; normalize).

Tactic Notation "exfalso" := apply poly_exfalso.

(** Solve by inverts *)
Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with
      | S (S (?n')) => subst; solve_by_inverts (S n') 
      | S O => subst; simpl in *; eauto
      end ]
  end end.

Ltac solve_by_invert := solve_by_inverts (S O).

(** Revert until *)
Ltac on_last_hyp tac :=
  match goal with [ H : _ |- _ ] => first [ tac H | fail 1 ] end.

Ltac revert_until id :=
  on_last_hyp ltac:(fun id' =>
    match id' with
      | id => idtac
      | _ => revert id' ; revert_until id
    end).

(** Exploit a lemma *)
Lemma mp : forall P Q : Type, P -> (P -> Q) -> Q.
Proof. intuition. Defined.
Ltac exploit x := eapply mp; [eapply x|].