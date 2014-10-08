Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require "Char".
Require Import "Definition".

Import ListNotations.

(** Export to a standard string. *)
Fixpoint to_string (s : t) : String.string :=
  match s with
  | [] => String.EmptyString
  | c :: s => String.String c (to_string s)
  end.

(** Import a standard string. *)
Fixpoint of_string (s : String.string) : t :=
  match s with
  | String.EmptyString => []
  | String.String c s => c :: of_string s
  end.

(** Alias. *)
Definition s := of_string.

Module OfNat.
  Require Import Program.
  Import Arith Div2.

  Lemma of_nat_lemma : forall m n, 1 < m -> ~ n < m -> 0 < n.
    destruct n; destruct m; intros.
    inversion H. exfalso. apply H0. etransitivity. 2: eassumption. repeat constructor.
    inversion H.
    eapply neq_0_lt. congruence.
  Qed.

  Program Fixpoint of_nat_aux (mod : nat) (_ : 1 < mod) (n : nat) {measure n} : t :=
    match NPeano.ltb n mod as x return NPeano.ltb n mod = x -> t with
      | true => fun _ => [Char.digit n]
      | false => fun pf =>
        let m := NPeano.div n mod in
        Char.digit (n - 10 * m) :: of_nat_aux mod _ m
    end eq_refl.
  Next Obligation.
    eapply NPeano.Nat.div_lt; auto.
    apply of_nat_lemma with (m := mod); trivial.
    intro Hlt.
    assert (Htrue := proj2 (NPeano.ltb_lt _ _) Hlt); congruence.
  Defined.
End OfNat.

Definition of_nat (mod : nat) (H : 1 < mod) (n : nat) : t :=
  List.rev' (OfNat.of_nat_aux mod H n).

Definition of_nat_2 (n : nat) : t.
  refine (of_nat 2 _ n).
  repeat constructor.
Defined.

Definition of_nat_8 (n : nat) : t.
  refine (of_nat 8 _ n).
  repeat constructor.
Defined.

Definition of_nat_10 (n : nat) : t.
  refine (of_nat 10 _ n).
  repeat constructor.
Defined.

Definition of_nat_16 (n : nat) : t.
  refine (of_nat 16 _ n).
  repeat constructor.
Defined.