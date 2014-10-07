Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.

Require Export ListStringComparison.
Require Export ListStringDefinition.

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

Fixpoint split_aux (s : t) (c : ascii) (beginning : t) : list t :=
  match s with
  | [] => [List.rev' beginning]
  | c' :: s =>
    if Ascii.eqb c c' then
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
      if Ascii.eqb c c' then
        List.rev' beginning :: split_limit_aux s c [] limit
      else
        split_limit_aux s c (c' :: beginning) (S limit)
    end
  end.

(** Split a string at each occurrence of a given character in a list of up to
    [limit] elements. *)
Definition split_limit (s : t) (c : ascii) (limit : nat) : list t :=
  split_limit_aux s c [] limit.

Module Tests.
  Local Open Scope char.

  Definition test_to_string :
    to_string ["h"; "e"; "l"; "l"; "o"] = "hello" %string :=
    eq_refl.

  Definition test_of_string :
    of_string "hello" = ["h"; "e"; "l"; "l"; "o"] :=
    eq_refl.

  Definition test_split_1 :
    split (of_string "go stop go") " " =
      [of_string "go"; of_string "stop"; of_string "go"] :=
    eq_refl.

  Definition test_split_2 :
    split (of_string "grr") " " = [of_string "grr"] :=
    eq_refl.
End Tests.