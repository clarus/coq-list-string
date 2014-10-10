Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.

Import ListNotations.
Local Open Scope char.

Module Sugar.
  Require "Conversion".
  Definition s := Conversion.s.
End Sugar.
Definition s := Sugar.s.

Module List.
  Fixpoint map_pair (A B C : Type) (f : A -> B -> C) (l : list (A * B))
    : list C :=
    match l with
    | [] => []
    | (x, y) :: l => f x y :: map_pair _ _ _ f l
    end.
  Arguments map_pair [A B C] _ _.

  Fixpoint map_triple (A B C D : Type) (f : A -> B -> C -> D)
    (l : list (A * B * C)) : list D :=
    match l with
    | [] => []
    | (x, y, z) :: l => f x y z :: map_triple _ _ _ _ f l
    end.
  Arguments map_triple [A B C D] _ _.
End List.

Module Case.
  Require Import "Case".

  Definition test_capitalize :
    List.map capitalize [s ""; s "A"; s "aAgZ,3%"] = [s ""; s "A"; s "AAgZ,3%"] :=
    eq_refl.

  Definition test_down_case :
    List.map down_case [s ""; s "aAgZ,3%"] = [s ""; s "aagz,3%"] :=
    eq_refl.

  Definition test_up_case :
    List.map up_case [s ""; s "aAgZ,3%"] = [s ""; s "AAGZ,3%"] :=
    eq_refl.
End Case.

Module Char.
  Require Import "Char".

  Definition test_digit :
    List.map digit [0; 1; 5; 9; 10; 12; 23] =
      ["0"; "1"; "5"; "9"; "A"; "C" ; "N"] :=
    eq_refl.

  Definition test_is_ascii :
    List.map is_ascii ["A"; "?"; """"; "010"; "127"; "128"; "255"] =
      [true; true; true; true; true; false; false] :=
      eq_refl.

  Definition test_is_white_space :
    List.map is_white_space [" "; "010"; "r"; ","] =
      [true; true; false; false] :=
      eq_refl.

  Definition test_down_case :
    List.map down_case ["a"; "A"; "g"; "Z"; ","; """"; "128"; "255"] =
      ["a"; "a"; "g"; "z"; ","; """"; "128"; "255"] :=
      eq_refl.

  Definition test_up_case :
    List.map up_case ["a"; "A"; "g"; "Z"; ","; """"; "128"; "255"] =
      ["A"; "A"; "G"; "Z"; ","; """"; "128"; "255"] :=
      eq_refl.
End Char.

Module Comparison.
  (* TODO *)
End Comparison.

Module Conversion.
  Require Import "Conversion".

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
End Conversion.

Module Etc.
  Require Import "Etc".

  Definition test_is_ascii :
    List.map is_ascii [s ""; s "ahah"; "128" :: s "ahah"] = [true; true; false] :=
    eq_refl.

  Definition test_is_empty :
    List.map is_empty [s ""; s "aAgZ"] = [true; false] :=
    eq_refl.

  Definition test_repeat :
    List.map_pair repeat [(s "", 0); (s "", 2); (s "ab", 0); (s "ab", 2)] =
      [s ""; s ""; s ""; s "abab"] :=
      eq_refl.

  Definition test_center :
    List.map_pair center [(s "", 4); (s "a", 4); (s "ab", 4); (s "abcd", 4);
      (s "abcde", 4); (s "ab", 0)] = [
      s "    "; s " a  "; s " ab "; s "abcd"; s "abcde"; s "ab"] :=
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

  Definition test_split_limit :
    List.map_triple split_limit [
      (s "", " ", 2);
      (s "go stop go", " ", 0);
      (s "go stop go ", " ", 3);
      (s "go stop go  ", " ", 1);
      (s "grr", " ", 4)] = [
      [s ""];
      [];
      [s "go"; s "stop"; s "go "];
      [s "go stop go  "];
      [s "grr"]] :=
    eq_refl.
End Etc.

Module Trim.
  Require Import "Trim".

  Definition test_chomp :
    List.map chomp [s ""; s "aa"; s "aa "; s "aa" ++ ["010"];
      s "aa" ++ ["010"; "013"]; s "aa" ++ ["013"; "010"]] =
      [s ""; s "aa"; s "aa "; s "aa"; s "aa" ++ ["010"]; s "aa"] :=
    eq_refl.

  Definition test_trim_head :
    List.map trim_head [s ""; s "aa"; s "a "; s " aa"; s "  a"; "011" :: s "aa"] =
      [s ""; s "aa"; s "a "; s "aa"; s "a"; s "aa"] :=
    eq_refl.

  Definition test_trim_tail :
    List.map trim_tail [s ""; s "aa"; s "a "; s " aa"; s "a  "; "011" :: s "aa"] =
      [s ""; s "aa"; s "a"; s " aa"; s "a"; "011" :: s "aa"] :=
    eq_refl.

  Definition test_trim :
    List.map trim [s ""; s "aa"; s "a "; s " aa"; s "a  "; "011" :: s "aa"] =
      [s ""; s "aa"; s "a"; s "aa"; s "a"; s "aa"] :=
    eq_refl.
End Trim.