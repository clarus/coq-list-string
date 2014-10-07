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

  Lemma compare_sound : forall (x y : bool), compare x y = Eq <-> x = y.
    intros x y; destruct x; destruct y; simpl; split; congruence.
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

  Lemma compare_sound : forall (x y : Ascii.ascii), compare x y = Eq <-> x = y.
    intros x y;
      destruct x as [x0 x1 x2 x3 x4 x5 x6 x7];
      destruct y as [y0 y1 y2 y3 y4 y5 y6 y7]; split; simpl.
    - intro Hcomp7.
      destruct (compose_compare_eq _ _ Hcomp7) as [Hcomp6 H7];
      destruct (compose_compare_eq _ _ Hcomp6) as [Hcomp5 H6];
      destruct (compose_compare_eq _ _ Hcomp5) as [Hcomp4 H5];
      destruct (compose_compare_eq _ _ Hcomp4) as [Hcomp3 H4];
      destruct (compose_compare_eq _ _ Hcomp3) as [Hcomp2 H3];
      destruct (compose_compare_eq _ _ Hcomp2) as [Hcomp1 H2];
      destruct (compose_compare_eq _ _ Hcomp1) as [H0 H1].
      rewrite (proj1 (Bool.compare_sound _ _) H0);
      rewrite (proj1 (Bool.compare_sound _ _) H1);
      rewrite (proj1 (Bool.compare_sound _ _) H2);
      rewrite (proj1 (Bool.compare_sound _ _) H3);
      rewrite (proj1 (Bool.compare_sound _ _) H4);
      rewrite (proj1 (Bool.compare_sound _ _) H5);
      rewrite (proj1 (Bool.compare_sound _ _) H6);
      rewrite (proj1 (Bool.compare_sound _ _) H7).
      reflexivity.
    - intro Heq; injection Heq; intros H7 H6 H5 H4 H3 H2 H1 H0.
      rewrite (proj2 (Bool.compare_sound _ _) H0);
      rewrite (proj2 (Bool.compare_sound _ _) H1);
      rewrite (proj2 (Bool.compare_sound _ _) H2);
      rewrite (proj2 (Bool.compare_sound _ _) H3);
      rewrite (proj2 (Bool.compare_sound _ _) H4);
      rewrite (proj2 (Bool.compare_sound _ _) H5);
      rewrite (proj2 (Bool.compare_sound _ _) H6);
      rewrite (proj2 (Bool.compare_sound _ _) H7).
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

Definition eqb (x y : t) : bool :=
  match compare x y with
  | Eq => true
  | _ => false
  end.

Lemma string_dec_sound : forall x y, eqb x y = true <-> x = y.
  induction x; destruct y; unfold eqb; simpl; split; try congruence.
  - case_eq (compose_compare (Ascii.compare a a0) (compare x y)); intro H; try congruence.
    destruct (compose_compare_eq _ _ H) as [Hchar Hstring].
    rewrite (proj1 (Ascii.compare_sound _ _) Hchar).
    assert (Hstring' : eqb x y = true); [unfold eqb; now rewrite Hstring |].
    now rewrite (proj1 (IHx _) Hstring').
  - intro Heq; injection Heq; intros Hstring Hchar.
    rewrite (proj2 (Ascii.compare_sound _ _) Hchar).
    assert (H := proj2 (IHx  _) Hstring).
    unfold eqb in H.
    congruence.
    
    try (unfold eqb; simpl; congruence).
  unfold eqb; simpl.
  destruct (Ascii.compare a a0); try congruence.
congruence.
  unfold eqb. simpl.
trivial.
trivial.
intuition.
tauto.
intuition.
  intros x y; split.
  - admit.
  - intro Heq.
  
  induction l; destruct r; simpl; split; try solve [ intuition ; congruence ];
  consider (ascii_dec a a0); intros; subst. f_equal. eapply IHl; auto.
  apply IHl. congruence.
  inversion H. congruence.
Qed.

(*Global Instance RelDec_string : RelDec (@eq string) :=
{| rel_dec := string_dec |}.

Global Instance RelDec_Correct_string : RelDec_Correct RelDec_string.
Proof.
  constructor; auto using string_dec_sound.
Qed.

Global Instance Reflect_string_dec a b : Reflect (string_dec a b) (a = b) (a <> b).
Proof.
  apply iff_to_reflect; auto using string_dec_sound.
Qed.*)