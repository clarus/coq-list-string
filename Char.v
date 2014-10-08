Require Import Strings.Ascii.
Require "Bool".

Local Open Scope char.

Definition compose_compare (x y : comparison) : comparison :=
  match x with
  | Eq => y
  | _ => x
  end.

Local Notation "x >> y" := (compose_compare x y) (only parsing, at level 30).

Lemma compose_compare_eq : forall (x y : comparison), compose_compare x y = Eq -> x = Eq /\ y = Eq.
  intros x y; destruct x; destruct y; simpl; split; congruence.
Qed.

Definition compare (x y : Ascii.ascii) : comparison :=
  match x, y with
  | Ascii.Ascii x1 x2 x3 x4 x5 x6 x7 x8,
    Ascii.Ascii y1 y2 y3 y4 y5 y6 y7 y8 =>
    Bool.compare x1 y1 >> Bool.compare x2 y2 >> Bool.compare x3 y3 >> Bool.compare x4 y4 >>
    Bool.compare x5 y5 >> Bool.compare x6 y6 >> Bool.compare x7 y7 >> Bool.compare x8 y8
  end.

Lemma compare_implies_eq : forall (x y : Ascii.ascii), compare x y = Eq -> x = y.
  intros x y;
    destruct x as [x0 x1 x2 x3 x4 x5 x6 x7];
    destruct y as [y0 y1 y2 y3 y4 y5 y6 y7]; simpl.
  intro Hcomp7.
  destruct (compose_compare_eq _ _ Hcomp7) as [Hcomp6 H7];
  destruct (compose_compare_eq _ _ Hcomp6) as [Hcomp5 H6];
  destruct (compose_compare_eq _ _ Hcomp5) as [Hcomp4 H5];
  destruct (compose_compare_eq _ _ Hcomp4) as [Hcomp3 H4];
  destruct (compose_compare_eq _ _ Hcomp3) as [Hcomp2 H3];
  destruct (compose_compare_eq _ _ Hcomp2) as [Hcomp1 H2];
  destruct (compose_compare_eq _ _ Hcomp1) as [H0 H1].
  rewrite (Bool.compare_implies_eq _ _ H0);
  rewrite (Bool.compare_implies_eq _ _ H1);
  rewrite (Bool.compare_implies_eq _ _ H2);
  rewrite (Bool.compare_implies_eq _ _ H3);
  rewrite (Bool.compare_implies_eq _ _ H4);
  rewrite (Bool.compare_implies_eq _ _ H5);
  rewrite (Bool.compare_implies_eq _ _ H6);
  rewrite (Bool.compare_implies_eq _ _ H7).
  reflexivity.
Qed.

Lemma compare_same_is_eq : forall (x : Ascii.ascii), compare x x = Eq.
  intro x; destruct x as [x0 x1 x2 x3 x4 x5 x6 x7]; simpl.
  now repeat (rewrite Bool.compare_same_is_eq).
Qed.

Definition eqb (x y : Ascii.ascii) : bool :=
  match compare x y with
  | Eq => true
  | _ => false
  end.

Definition digit (n : nat) : Ascii.ascii :=
  match n with
  | 0 => "0"
  | 1 => "1"
  | 2 => "2"
  | 3 => "3"
  | 4 => "4"
  | 5 => "5"
  | 6 => "6"
  | 7 => "7"
  | 8 => "8"
  | 9 => "9"
  | n => Ascii.ascii_of_nat (n - 9 + nat_of_ascii "A")
  end.