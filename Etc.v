Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require "Char".
Require Import "Comparison".
Require Import "Definition".

Import ListNotations.

(** Test if the string contains only ASCII characters. *)
Definition is_ascii (s : t) : bool :=
  List.forallb Char.is_ascii s.

(** Convert the first character to uppercase. *)
Definition capitalize (s : t) : t :=
  match s with
  | [] => []
  | c :: s => Char.up_case c :: s
  end.

(** Replace uppercase letters by lowercase ones (only characters from a to z are affected). *)
Definition down_case (s : t) : t :=
  List.map Char.down_case s.

(** Replace lowercase letters by uppercase ones (only characters from a to z are affected). *)
Definition up_case (s : t) : t :=
  List.map Char.up_case s.

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