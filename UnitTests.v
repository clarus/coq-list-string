Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import "ListString".

Import ListNotations.
Import ListString.
Local Open Scope char.

Definition test_to_string :
  to_string ["h"; "e"; "l"; "l"; "o"] = "hello" % string :=
  eq_refl.

Definition test_of_string :
  of_string "hello" = ["h"; "e"; "l"; "l"; "o"] :=
  eq_refl.

Definition test_split_1 :
  split (s "go stop go") " " =
    [s "go"; s "stop"; s "go"] :=
  eq_refl.

Definition test_split_2 :
  split (s "grr") " " = [s "grr"] :=
  eq_refl.