Require Coq.Arith.Div2.
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require "Char".
Require Import "Comparison".
Require Import "Definition".

Import ListNotations.
Local Open Scope char.

(** Test if the string contains only ASCII characters. *)
Definition is_ascii (s : t) : bool :=
  List.forallb Char.is_ascii s.

(** Test if the string is empty. *)
Definition is_empty (s : t) : bool :=
  match s with
  | [] => true
  | _ :: _ => false
  end.

(** Repeat a string [n] times. *)
Fixpoint repeat (s : t) (n : nat) : t :=
  match n with
  | O => []
  | S n => s ++ repeat s n
  end.

(** Center a string on a line of width [width], with white space paddings. *)
Definition center (s : t) (width : nat) : t :=
  let l := List.length s in
  let l_left := Div2.div2 (width - l) in
  let l_right := (width - l) - l_left in
  repeat [" "] l_left ++ s ++ repeat [" "] l_right.

Fixpoint split_aux (s : t) (c : ascii) (beginning : t) : list t :=
  match s with
  | [] => [List.rev' beginning]
  | c' :: s =>
    if Char.eqb c c' then
      List.rev' beginning :: split_aux s c []
    else
      split_aux s c (c' :: beginning)
  end.

(** Split a string at each occurrence of a given character. *)
Definition split (s : t) (c : ascii) : list t :=
  split_aux s c [].

Fixpoint split_limit_aux (s : t) (c : ascii) (beginning : t) (limit : nat)
  : list t :=
  match limit with
  | O => []
  | S O => [List.rev' beginning ++ s]
  | S limit =>
    match s with
    | [] => [List.rev' beginning]
    | c' :: s =>
      if Char.eqb c c' then
        List.rev' beginning :: split_limit_aux s c [] limit
      else
        split_limit_aux s c (c' :: beginning) (S limit)
    end
  end.

(** Split a string at each occurrence of a given character in a list of up to
    [limit] elements. *)
Definition split_limit (s : t) (c : ascii) (limit : nat) : list t :=
  split_limit_aux s c [] limit.