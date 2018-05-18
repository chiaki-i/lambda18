Require Import Cpdt.CpdtTactics.
Require Import Cpdt.Subset.
Require Import Cpdt.MoreSpecif.

(* 1番は eq_nat_dec の少し違うバージョン *)
Definition leq_or_greater : forall n m : nat, {n <= m} + {n > m}.
  refine (fix f (n m : nat) : {n <= m} + {n > m} :=
            match n, m with
            | O, O => Yes       (* 左側 *)
            | O, S m' => Yes    (* 左側 *)
            | S n', O => No     (* 右側 *)
            | S n', S m' => Reduce (f n' m') (* 再帰 *)
            end); intuition.
Defined.

(* 2-a *)
