Require Import Arith Bool List Omega.
Require Import Cpdt.CpdtTactics Cpdt.MoreDep.

Require Extraction.
Set Implicit Arguments.
(* Set Asymetric Patterns. *)


Section ilist.
  Variable A : Set.

  Inductive ilist : nat -> Set :=
  | Nil : ilist O
  | Cons : forall n, A -> ilist n -> ilist (S n).

  Fixpoint app n1 (ls1 : ilist n1) n2 (ls2 : ilist n2) : ilist (n1 + n2) :=
    match ls1 in (ilist n1) return (ilist (n1 + n2)) with
    | Nil => ls2
    | Cons x ls1' => Cons x (app ls1' ls2)
    end.
  (* Set Implicit Arguments. とファイルの最初に書けば
     Cons は引数が２つの関数と解釈される *)

  Definition hd' n (ls : ilist n) :=
    match ls in (ilist n) return (match n with O => unit | S _ => A end) with
    | Nil => tt
    | Cons h _ => h
    end.

  Definition hd n (ls : ilist (S n)) : A := hd' ls.
End ilist.

Section Exercise.
  Variable A B : Set.

  Fixpoint map {n} (f : A -> B) (lst : ilist A n) : ilist B n :=
    match lst with
    | Nil _ => Nil _
    | Cons x xs => Cons (f x) (map f xs)
    end.

  Fixpoint concat {m n} (lst1 : ilist (ilist A m) n) : ilist A (n * m) :=
    match lst1 with
    | Nil _ => Nil _
    | Cons x xs => app x (concat xs)
    end.
End Exercise.