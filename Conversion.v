Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
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