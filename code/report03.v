Require Import Cpdt.CpdtTactics.
Require Import Cpdt.Predicates.
(* exercise 0.2-1
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
      
(* exercise 0.2-2 *)
Theorem first_order_logic : forall (A : Type) (x y z : A) (P : A -> Prop)
                                   (Q : A -> A -> Prop) (F : A -> A),
    (P x) -> (forall x, P x -> exists y, Q x y) ->
    (forall x y, Q x y -> Q y (F y)) ->
    (exists z, Q z (F z)).
  intros.
  apply H0 in H.                (* 前提が forall なら apply *)
  destruct H as [ y0 H2 ].      (* 前提が exists なら destruct/case *)
  apply H1 in H2.
  exists y0.                    (* exists を示したければ具体的に成り立つものを与える *)
  assumption.
Qed.

Section Two.                    (* こう書くと綺麗 *)
  Variable T : Set.
  Variable x : T.
  Variable p : T -> Prop.
  Variable q : T -> T -> Prop.
  Variable f : T -> T.

  Theorem ex : p x -> (forall x, p x -> exists y, q x y) ->
               (forall x y, q x y -> q y (f y)) -> exists z, q z (f z).
    intros.
    assert (exists y, q x y).
    apply H0; assumption.
    destruct H2.
    exists x0.
    eapply H1.                  (* 普通のapplyだと死ぬ メタ変数を入れるようにする *)
    eassumption.
  Qed.
End Two.

(* exercise 0.2-3 *)
Inductive mult6 : nat -> Prop :=
| Mult6   : mult6 O
| MultS6  : forall n, mult6 n -> mult6 (S (S (S (S (S (S n)))))).

Inductive mult10 : nat -> Prop :=
| Mult10  : mult10 O
| MultS10 : forall n, mult10 n -> mult10 (S (S (S (S (S (S (S (S (S (S n)))))))))).

Inductive multiple : nat -> Prop :=
| Multi6  : forall n, mult6 n -> multiple n
| Multi10 : forall n, mult10 n -> multiple n.

Theorem mult6_contra : mult6 13 -> False.
  inversion 1.
  inversion H1.
  inversion H3.
Qed.

Theorem not13 : ~ (mult6 13).   (* False を導いても、not を示してもOK *)
  intro.
  repeat (
      match goal with
      | [ H : mult6  ?N |- _] => inversion H
      | [ H : mult10 ?N |- _] => inversion H
      end
    ).
Qed.
  
Theorem multiple_contra : multiple 13 -> False.
  inversion 1.
  inversion H0.
  inversion H3.
  inversion H5.

  inversion H0.
  inversion H3.
Qed.

Inductive oddness : nat -> Prop :=
| Odd : forall n, oddness (S (n * 2)).

Eval simpl in oddness (S O).
Eval simpl in (S (S (S O)) * 2).

Theorem not_6_or_10 : forall n, multiple n -> ~ exists m, n = 1 + 2 * m.
  Admitted.