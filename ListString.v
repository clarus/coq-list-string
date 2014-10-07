Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.

Import ListNotations.

Definition t : Set := list Ascii.ascii.

Fixpoint to_string (s : t) : String.string :=
  match s with
  | [] => String.EmptyString
  | c :: s => String.String c (to_string s)
  end.

Fixpoint of_string (s : String.string) : t :=
  match s with
  | String.EmptyString => []
  | String.String c s => c :: of_string s
  end.

Definition compose_compare (x y : comparison) : comparison :=
  match x with
  | Eq => y
  | _ => x
  end.

Local Notation "x >> y" := (compose_compare x y) (only parsing, at level 30).

Lemma compose_compare_eq : forall (x y : comparison), compose_compare x y = Eq -> x = Eq /\ y = Eq.
  intros x y; destruct x; destruct y; simpl; split; congruence.
Qed.

Module Bool.
  Definition compare (x y : bool) : comparison :=
    match x, y with
    | true, false => Gt
    | false, true => Lt
    | true, true | false, false => Eq
    end.

  Lemma compare_same_is_eq : forall (x : bool), compare x x = Eq.
    intro x; destruct x; simpl; reflexivity.
  Qed.

  Lemma compare_implies_eq : forall (x y : bool), compare x y = Eq -> x = y.
    intros x y; destruct x; destruct y; simpl; congruence.
  Qed.
End Bool.

Module Ascii.
  Definition compare (x y : Ascii.ascii) : comparison :=
    match x, y with
    | Ascii.Ascii x1 x2 x3 x4 x5 x6 x7 x8,
      Ascii.Ascii y1 y2 y3 y4 y5 y6 y7 y8 =>
      Bool.compare x1 y1 >> Bool.compare x2 y2 >> Bool.compare x3 y3 >> Bool.compare x4 y4 >>
      Bool.compare x5 y5 >> Bool.compare x6 y6 >> Bool.compare x7 y7 >> Bool.compare x8 y8
    end.

  Lemma compare_same_is_eq : forall (x : Ascii.ascii), compare x x = Eq.
    intro x; destruct x as [x0 x1 x2 x3 x4 x5 x6 x7]; simpl.
    now repeat (rewrite Bool.compare_same_is_eq).
  Qed.

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
End Ascii.

Fixpoint compare (x y : t) : comparison :=
  match x, y with
  | [], [] => Eq
  | [], _ => Lt
  | _, [] => Gt
  | x :: xs, y :: ys => Ascii.compare x y >> compare xs ys
  end.

Lemma compare_same_is_eq : forall (x : t), compare x x = Eq.
  intro x; induction x; simpl; trivial.
  now rewrite Ascii.compare_same_is_eq; rewrite IHx.
Qed.

Lemma compare_implies_eq : forall (x y : t), compare x y = Eq -> x = y.
  induction x as [|a x HI]; destruct y as [|b y]; simpl; try congruence.
  case_eq (Ascii.compare a b); simpl; try congruence.
  now intros Hab Hxy; rewrite (Ascii.compare_implies_eq _ _ Hab); rewrite (HI _ Hxy).
Qed.

Definition eqb (x y : t) : bool :=
  match compare x y with
  | Eq => true
  | _ => false
  end.

Lemma eqb_same_is_eq : forall (x : t), eqb x x = true.
  now intros; unfold eqb; rewrite compare_same_is_eq.
Qed.

Lemma eqb_implies_eq : forall (x y : t), eqb x y = true -> x = y.
  intros x y; unfold eqb; case_eq (compare x y); try congruence.
  now intros; apply compare_implies_eq.
Qed.

Definition eq_dec (x y : t) : {x = y} + {x <> y}.
  case_eq (eqb x y); intro Heqb; [left | right].
  - now apply eqb_implies_eq.
  - intro Heq; rewrite Heq in Heqb.
    rewrite eqb_same_is_eq in Heqb; congruence.
Qed.