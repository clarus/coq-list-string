# coq-list-string
Strings implemented as lists. Finally.

## Install
### With OPAM
Add the Coq repository:

    opam repo add coq https://github.com/coq/opam-coq-repo.git

and run:

    opam install coq-list-string

### From the sources
Do a classic:

    ./configure.sh
    make
    make install

## Use
Add:

    Require LString.LString.

at the beginning of your source files. The library will be available under the `LString` module. It defines the type `LString.t` of strings encoded as lists of ASCII 8-bits characters. To define a string you can either define a list:

    ["h"; "e"; "l"; "l"; "o"] : LString.t

or import a Coq `string` using the string notation:

    LString.s "hello" : LString.t

## Reference
* `capitalize (s : t) : t`
  Convert the first character to uppercase.
* `down_case (s : t) : t`
  Replace uppercase letters by lowercase ones (only characters from a to z are affected).
* `up_case (s : t) : t`
  Replace lowercase letters by uppercase ones (only characters from a to z are affected).

* `Char.compare (x y : Ascii.ascii) : comparison`
  Total order on characters.
  * `Char.compare_implies_eq : forall (x y : Ascii.ascii), compare x y = Eq -> x = y`
  * `Char.compare_same_is_eq : forall (x : Ascii.ascii), compare x x = Eq`
* `Char.eqb (x y : Ascii.ascii) : bool`
  Test if two characters are equal.
* `Char.digit (n : nat) : Ascii.ascii`
  The character of a digit (0, 1, ..., 9, A, B, ...).
* `Char.is_ascii (c : Ascii.ascii) : bool`
  Test if the character is in the ASCII range.
* `Char.is_white_space (c : Ascii.ascii) : bool`
  Test if the character is a white space (space, \t, \n, \v, \f or \r).
* `Char.down_case (c : Ascii.ascii) : Ascii.ascii`
  Replace uppercase letters by lowercase ones (only characters from a to z are affected).
* `Char.up_case (c : Ascii.ascii) : Ascii.ascii`
  Replace lowercase letters by uppercase ones (only characters from a to z are affected).

* `compare (x y : t) : comparison`
  Total order on strings.
  * `compare_implies_eq : forall (x y : t), compare x y = Eq -> x = y`
  * `compare_same_is_eq : forall (x : t), compare x x = Eq`
* `eqb (x y : t) : bool`
  Test if two strings are equal.
  * `eqb_implies_eq : forall (x y : t), eqb x y = true -> x = y`
  * `eqb_same_is_eq : forall (x : t), eqb x x = true`
* `eq_dec (x y : t) : {x = y} + {x <> y}`
  Decide the equality of two strings.

* `to_string (s : t) : String.string`
  Export to a standard string.
* `of_string (s : String.string) : t`
  Import a standard string. See the [s] alias.
* `s (s : String.string) : t`
  Alias for [of_string].
* `of_nat (mod : nat) (H : 1 < mod) (n : nat) : t`
  Convert an integer to a string in base [mod].
* `of_nat_2 (n : nat) : t`
  Convert an integer to a string in base 2.
* `of_nat_8 (n : nat) : t`
  Convert an integer to a string in base 8.
* `of_nat_10 (n : nat) : t`
  Convert an integer to a string in base 10.
* `of_nat_16 (n : nat) : t`
  Convert an integer to a string in base 16.

* `t : Set := list Ascii.ascii`
  A string is a list of characters.

* `is_ascii (s : t) : bool`
  Test if the string contains only ASCII characters.
* `is_empty (s : t) : bool`
  Test if the string is empty.
* `repeat (s : t) (n : nat) : t`
  Repeat a string [n] times.
* `center (s : t) (width : nat) : t`
  Center a string on a line of width [width], with white space paddings.
* `split (s : t) (c : ascii) : list t`
  Split a string at each occurrence of a given character. 
* `split_limit (s : t) (c : ascii) (limit : nat) : list t`
  Split a string at each occurrence of a given character in a list of up to [limit] elements.

* `chomp (s : t) : t`
  Remove one end of line at the end, if present (can be \n, \r or \r\n).
* `trim_head (s : t) : t`
  Remove white spaces at the beginning of a string (spaces, \t, \n, \v, \f or \r).
* `trim_tail (s : t) : t`
  Remove white spaces at the end of a string (spaces, \t, \n, \v, \f or \r).
* `trim (s : t) : t`
  Remove white spaces at the beginning and the end of a string (spaces, \t, \n, \v, \f or \r).