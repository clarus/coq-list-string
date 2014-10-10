Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.

(** The definition of a string is embedded into a module name [LString] so that
    on typing the user gets the inferred type [Definition.LString.t] instead of
    [Definition.t]. *)
Module LString.
  (** A string is a list of characters. *)
  Definition t : Set := list Ascii.ascii.
End LString.