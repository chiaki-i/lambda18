Require Import Cpdt.CpdtTactics.
Require Import Cpdt.Predicates.
(* exercise 0.2 (1)
   以下に示したタクティクのみを用いて、(a) ~ (c) を証明せよ。
   apply, assumption, constructor, destruct, intro, intros, left, right, split, unfold *)

Theorem tautology_a : and (or True False) (or True False).
  constructor; constructor; apply I.
Qed.

Theorem tautology_b : forall P : Prop, P -> ~ ~ P.
  intros.
  unfold not.
  intro.
  apply H0, H.
Qed.

Theorem tautology_c : forall P Q R : Prop, (and P (or Q R)) -> (or (and P Q) (and P R)).
  intros.
  destruct H.
  destruct H0.
  left.
  constructor.
  apply H.
  apply H0.
  right.
  constructor.
  apply H.
  apply H0.
Qed.

(* exercise 0.2
   一階論理の式
 *)
Theorem first_order_logic : forall (A : Type) (x y z : A) (P : A -> Prop)
                                   (Q : A -> A -> Prop) (F : A -> A),
    (P x) -> (forall x, P x -> exists y, Q x y) ->
    (forall x y, Q x y -> Q y (F y)) ->
    (exists z, Q z (F z)).
  intros.
  assert (forall x : A, P x -> Q x y).
  apply H0.
  apply H0 in H.
  assert (Q x y).
  apply H.
  apply H1 in H.
  
  assert (exists (x y : A), Q x y).
  
  assert (exists (x y : A), Q x y -> Q y (F y)).

  apply H1.
  intro.