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
  split (of_string "go stop go") " " =
    [of_string "go"; of_string "stop"; of_string "go"] :=
  eq_refl.

Definition test_split_2 :
  split (of_string "grr") " " = [of_string "grr"] :=
  eq_refl.