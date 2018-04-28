Require Import Cpdt.CpdtTactics.
(* Ex 0.1 *)
(* A and B = B and A *)
(* A and (B or C) ≡ (A and B) or (A and C) *)

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
Require Import List.

Section slist.
  Variable T : Set.

  (* Inductive list : Set := *)
  (* | Nil : list *)
  (* | Cons : T -> list -> list. *)

  (* Fixpoint app (ls1 ls2 : list) : list := *)
  (*   match ls1 with *)
  (*   | Nil => ls2 *)
  (*   | Cons x ls1' => Cons x (app ls1' ls2) *)
  (*   end. *)
  
  Inductive slist : Set :=
  | SEmpty : slist
  | SSingle : T -> slist
  | SConcat : slist -> slist -> slist.
  
  Fixpoint flatten (sl : slist) : list T :=
    match sl with
    | SEmpty => nil             (* Nil ではなくて、もともとの nil を使えばいい *)
    | SSingle x => x :: nil
    | SConcat l₁ l₂ => (flatten l₁) ++ (flatten l₂)
    end.

  (* flatten (sl₁ ++ sl₂) = flatten sl₁ ++ flatten sl₂ *)
  Theorem flat_dist : forall sl₁ sl₂ : slist,
      flatten (SConcat sl₁ sl₂) = app (flatten sl₁) (flatten sl₂).
    (* なぜか app を ++ に変えるとうまくいかない *)
    induction sl₁; reflexivity.
  Qed.
End slist.
  
(* Ex 0.5 相互再帰 *)
Inductive even_nat : Set :=
| O  : even_nat
| ES : odd_nat -> even_nat
                    
with odd_nat : Set := 
     | OS : even_nat -> odd_nat.

Scheme even_nat_mutual := Induction for even_nat Sort Prop
                          with odd_nat_mutual := Induction for odd_nat Sort Prop.

Eval simpl in (OS O).     (* 1 : odd_nat *)
Eval simpl in (ES (OS (ES (OS O)))). (* 4 : even_nat *)

Fixpoint add_even_even (n m: even_nat) : even_nat :=
  match n with
  | O => m
  | ES n' => match m with
             | O => ES n'
             | ES m' => ES (OS (add_odd_odd n' m'))
             end
  end

with add_odd_odd (n m: odd_nat) : even_nat :=
       match n, m with
       | OS n', OS m' => ES (OS (add_even_even n' m'))
       end.

Eval simpl in (add_even_even O O).
Eval simpl in (add_even_even O (ES (OS O))).
Eval simpl in (add_even_even (ES (OS O)) O).
Eval simpl in (add_even_even (ES (OS O)) (ES (OS O))).

Lemma O_add_even_n : forall n : even_nat, add_even_even O n = n.
  intro; reflexivity.
Qed.

Theorem add_even_comm : forall n m : even_nat, add_even_even n m = add_even_even m n.
  apply (even_nat_mutual
    (fun (e1 : even_nat) => forall (e2 : even_nat),
         add_even_even e1 e2 = add_even_even e2 e1)
    (fun (o1 : odd_nat) => forall (o2 : odd_nat),
         add_odd_odd o1 o2 = add_odd_odd o2 o1)).
  induction e2; reflexivity.  
  induction e2. reflexivity.
  simpl. f_equal. f_equal.
  apply H.
  crush.  
  induction o2; simpl; f_equal. f_equal.
  apply H.
Qed.