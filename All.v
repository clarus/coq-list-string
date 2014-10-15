Require "Case".
Require "Comparison".
Require "Conversion".
Require "Etc".
Require "LString".
Require "Trim".

Module LString.
  Include LString.Case.
  Include LString.Comparison.
  Include LString.Conversion.
  Include LString.Etc.
  Include LString.LString.
  Include LString.Trim.

  Module Char.
    Require "Char".
    Include LString.Char.
  End Char.
End LString.