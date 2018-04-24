(* Ex 0.1 *)
(* A and B = B and A *)
(* A and (B or C) ≡ (A andd B) or (A and C) *)

Inductive truth : Set :=
| Yes : truth
| No : truth
| Maybe : truth.

Fixpoint not (a : truth) : truth :=
  match a with
  | Yes => No
  | No => Yes
  | Maybe => Maybe
  end.

Fixpoint and (a b : truth) : truth :=
  match a, b with
  | Yes, b    => b
  | No, b     => No
  | Maybe, No => No
  | Maybe, b  => Maybe
  end.

Fixpoint or (a b : truth) : truth :=
  match a, b with
  | Yes, b    => Yes
  | No, b     => b
  | Maybe, No => Maybe
  | Maybe, b  => b
  end.

Eval simpl in and Yes Yes.
Eval simpl in and Yes Maybe.
Eval simpl in and Yes No.
Eval simpl in and Maybe Yes.
Eval simpl in and Maybe Maybe.
Eval simpl in and Maybe No.
Eval simpl in and No Yes.
Eval simpl in and No Maybe.
Eval simpl in and No No.

Theorem and_commutative : forall a b : truth, and a b = and b a.
  destruct a, b; reflexivity.
Qed.

Theorem and_dist_or : forall a b c : truth, and a (or b c) = or (and a b) (and a c).
  destruct a, b, c; reflexivity.
Qed.

(* Ex 0.2 *)
(* flatten (sl₁ ++ sl₂) = flatten sl₁ ++ flatten sl₂ *)
Require Import List.

Inductive list (T : Set) : Set :=
| Nil : list T
| Cons : T -> list T -> list T.

Implicit Arguments Nil [T].

Fixpoint app T (ls1 ls2 : list T) : list T :=
  match ls1 with
    | Nil => ls2
    | Cons x ls1' => Cons x (app ls1' ls2)
  end.

Inductive slist (T : Set) : Set :=
| SEmpty : slist T
| SSingle : T -> slist T
| SConcat : slist T -> slist T -> slist T.

Fixpoint flatten T (sl : slist T) : list T :=
  match sl with
  | SEmpty _ => Nil
  | SSingle _ x => Cons x Nil
  | SConcat _ l₁ l₂ => App (flatten l₁) (flatten l₂)
  end.