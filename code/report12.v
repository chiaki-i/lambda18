(* 第12回課題
 * 先週の群論に関する問題を rewrite を用いて解く。
 * 実行例 : rewriter (rightId, (rightInv, tt)) 3
 *)

Require Import Bool List.
Require Import Cpdt.CpdtTactics.
Set Implicit Arguments.
Set Asymmetric Patterns.

Section group.
  Variable G : Set.
  Variable f : G -> G -> G.
  Infix "*" := f.

  Variable e : G.
  Variable i : G -> G.

  Variable assoc : forall a b c, (a * b) * c = a * (b * c).
  Variable rightId : forall a, a * e = a.
  Variable rightInv : forall a, a * i a = e.
  (* Set Ltac Debug.*)
  
  Ltac rewriter tacs n :=
    intros;
    let rec search lst :=
        match lst with
        | (?lemma, ?more) => try rewrite lemma; try search more
        | tt => fail 1
        end
    in
    match n with
    | O => try reflexivity
    | S ?n' => try search tacs; rewriter tacs n'
    end.
  
  Lemma test1 : forall a b, a * b * i b = a.
    rewriter (assoc, (rightInv, (rightId, tt))) 1.
  Qed.

  Lemma test2 : forall a, a * e * i a * i e = e.
    rewriter (rightInv, (rightId, tt)) 3.
  Qed.

End group.