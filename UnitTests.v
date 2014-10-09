Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import "ListString".

Import ListNotations.
Import ListString.
Local Open Scope char.

Module List.
  Fixpoint map_pair (A B C : Type) (f : A -> B -> C) (l : list (A * B))
    : list C :=
    match l with
    | [] => []
    | (x, y) :: l => f x y :: map_pair _ _ _ f l
    end.
  Arguments map_pair [A B C] _ _.
End List.

(** * Char *)
Module Char.
  Definition test_digit :
    List.map Char.digit [0; 1; 5; 9; 10; 12; 23] =
      ["0"; "1"; "5"; "9"; "A"; "C" ; "N"] :=
    eq_refl.

  Definition test_is_ascii :
    List.map Char.is_ascii ["A"; "?"; """"; "010"; "127"; "128"; "255"] =
      [true; true; true; true; true; false; false] :=
      eq_refl.

  Definition test_down_case :
    List.map Char.down_case ["a"; "A"; "g"; "Z"; ","; """"; "128"; "255"] =
      ["a"; "a"; "g"; "z"; ","; """"; "128"; "255"] :=
      eq_refl.

  Definition test_up_case :
    List.map Char.up_case ["a"; "A"; "g"; "Z"; ","; """"; "128"; "255"] =
      ["A"; "A"; "G"; "Z"; ","; """"; "128"; "255"] :=
      eq_refl.
End Char.

(** * Comparison *)

(** * Conversion *)
Definition test_to_string :
  List.map to_string [
    [];
    ["h"; "e"; "l"; "l"; "o"]] = [
    "";
    "hello"] % string :=
  eq_refl.

Definition test_of_string :
  List.map of_string [
    "";
    "hello"] % string = [
    [];
    ["h"; "e"; "l"; "l"; "o"]] :=
  eq_refl.

Definition test_of_nat_2 :
  List.map of_nat_2 [0; 1; 2; 3; 12; 23] =
    [s "0"; s "1"; s "10"; s "11"; s "1100"; s "10111"] :=
  eq_refl.

Definition test_of_nat_8 :
  List.map of_nat_8 [0; 1; 2; 3; 12; 23] =
    [s "0"; s "1"; s "2"; s "3"; s "14"; s "27"] :=
  eq_refl.

Definition test_of_nat_10 :
  List.map of_nat_10 [0; 1; 2; 3; 12; 23] =
    [s "0"; s "1"; s "2"; s "3"; s "12"; s "23"] :=
  eq_refl.

Definition test_of_nat_16 :
  List.map of_nat_16 [0; 1; 2; 3; 12; 23] =
    [s "0"; s "1"; s "2"; s "3"; s "C"; s "17"] :=
  eq_refl.

(** * Etc *)
Definition test_is_ascii :
  List.map is_ascii [s ""; s "ahah"; "128" :: s "ahah"] = [true; true; false] :=
  eq_refl.

Definition test_down_case :
  List.map down_case [s ""; s "aAgZ,3%"] = [s ""; s "aagz,3%"] :=
  eq_refl.

Definition test_up_case :
  List.map up_case [s ""; s "aAgZ,3%"] = [s ""; s "AAGZ,3%"] :=
  eq_refl.

Definition test_split :
  List.map_pair split [
    (s "", " ");
    (s "go stop go", " ");
    (s "go stop go ", " ");
    (s "go stop go  ", " ");
    (s "grr", " ")] = [
    [s ""];
    [s "go"; s "stop"; s "go"];
    [s "go"; s "stop"; s "go"; s ""];
    [s "go"; s "stop"; s "go"; s ""; s ""];
    [s "grr"]] :=
  eq_refl.