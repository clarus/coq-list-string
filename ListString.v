Require "Comparison".
Require "Conversion".
Require "Definition".
Require "Etc".

Include ListString.Comparison.
Include ListString.Conversion.
Include ListString.Definition.
Include ListString.Etc.

Module Char.
  Require "Char".
  Include ListString.Char.
End Char.