Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require "Char".
Require Import "LString".

Import ListNotations.
Import LString.

(** Export to a standard string. *)
Fixpoint to_string (s : t) : String.string :=
  match s with
  | [] => String.EmptyString
  | c :: s => String.String c (to_string s)
  end.

(** Import a standard string. See the alias [s]. *)
Fixpoint of_string (s : String.string) : t :=
  match s with
  | String.EmptyString => []
  | String.String c s => c :: of_string s
  end.

(** Alias for [of_string]. *)
Definition s := of_string.

Fixpoint of_n_aux (base : N) (digits : nat) (n : N) : t :=
  match digits with
  | O => []
  | S digits =>
    if N.eqb n 0 then
      []
    else
      Char.digit (N.modulo n base) :: of_n_aux base digits (N.div n base)
  end.

(** Convert an integer to a string in base [base] with up to [digits] digits. *)
Definition of_n (base : N) (digits : nat) (n : N) : t :=
  if N.eqb n 0 then
    s "0"
  else
    List.rev' (of_n_aux base digits n).

Module OfNat.
  Require Import Program.
  Import Arith Div2.

  Lemma of_nat_lemma : forall m n, 1 < m -> ~ n < m -> 0 < n.
    destruct n; destruct m; intros.
    inversion H. exfalso. apply H0. etransitivity. 2: eassumption. repeat constructor.
    inversion H.
    eapply neq_0_lt. congruence.
  Qed.

  Program Fixpoint of_nat_aux (base : nat) (_ : 1 < base) (n : nat) {measure n} : t :=
    match NPeano.ltb n base as x return NPeano.ltb n base = x -> t with
      | true => fun _ => [Char.digit (N.of_nat n)]
      | false => fun pf =>
        let m := NPeano.div n base in
        Char.digit (N.of_nat (n - base * m)) :: of_nat_aux base _ m
    end eq_refl.
  Next Obligation.
    eapply NPeano.Nat.div_lt; auto.
    apply of_nat_lemma with (m := base); trivial.
    intro Hlt.
    assert (Htrue := proj2 (NPeano.ltb_lt _ _) Hlt); congruence.
  Defined.
End OfNat.

(** Convert an integer to a string in base [base]. *)
Definition of_nat (base : nat) (H : 1 < base) (n : nat) : t :=
  List.rev' (OfNat.of_nat_aux base H n).

(** Convert an integer to a string in base 2. *)
Definition of_nat_2 (n : nat) : t.
  refine (of_nat 2 _ n).
  repeat constructor.
Defined.

(** Convert an integer to a string in base 8. *)
Definition of_nat_8 (n : nat) : t.
  refine (of_nat 8 _ n).
  repeat constructor.
Defined.

(** Convert an integer to a string in base 10. *)
Definition of_nat_10 (n : nat) : t.
  refine (of_nat 10 _ n).
  repeat constructor.
Defined.

(** Convert an integer to a string in base 16. *)
Definition of_nat_16 (n : nat) : t.
  refine (of_nat 16 _ n).
  repeat constructor.
Defined.