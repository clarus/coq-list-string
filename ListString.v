Require Import "Comparison".
Require Import "Conversion".
Require Import "Definition".
Require Import "Etc".

Module ListString.
  Include ListString.Comparison.
  Include ListString.Conversion.
  Include ListString.Definition.
  Include ListString.Etc.
End ListString.