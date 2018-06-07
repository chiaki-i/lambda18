Require Import Cpdt.CpdtTactics.
Require Import Cpdt.DataStruct.
Require Import Arith List.

Section hlist.
  Variable A : Type.
  Variable B : A -> Type.
  
  Inductive hlist : list A -> Type :=
  | HNil : hlist nil
  | HCons : forall (x : A) (ls : list A), B x -> hlist ls -> hlist (x :: ls).

  Fixpoint happ c1 (lst1 : hlist c1) c2 (lst2 : hlist c2) : hlist (app c1 c2) :=
    match lst1 with
    | HNil => lst2
    | HCons a la b lst1' => HCons a (la ++ c2) b (happ la lst1' c2 lst2)
    end.

  Print happ.
End hlist.