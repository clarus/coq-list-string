# ![Logo](https://raw.githubusercontent.com/clarus/icons/master/typewriter-48.png) List String
Strings implemented as lists. Finally.

## Install
### With OPAM
Add the Coq repository:

    opam repo add coq-stable https://github.com/coq/repo-stable.git

and run:

    opam install coq-list-string

### From the sources
Do a classic:

    ./configure.sh
    make
    make install

## Use
Add:

    Require Import LString.All.

at the beginning of your source files. The library will be available under the `LString` module. It defines the type `LString.t` of strings encoded as lists of ASCII 8-bits characters. To define a string you can either define a list:

    ["h"; "e"; "l"; "l"; "o"] : LString.t

or import a Coq `string` using the string notation:

    LString.s "hello" : LString.t

To have a nice pretty-printing of the strings, add:

    Require Import Coq.Strings.Ascii.
    Local Open Scope char.

at the beginning of your files.

## Reference
* `capitalize (s : t) : t` Convert the first character to uppercase.
* `center (s : t) (width : nat) : t` Center a string on a line of width `width`, with white space paddings.
* `chomp (s : t) : t` Remove one end of line at the end, if present (can be \n, \r or \r\n).
* `compare (x y : t) : comparison` Total order on strings.
  * `compare_implies_eq : forall (x y : t), compare x y = Eq -> x = y`
  * `compare_same_is_eq : forall (x : t), compare x x = Eq`
* `down_case (s : t) : t` Replace uppercase letters by lowercase ones (only characters from a to z are affected).
* `eq_dec (x y : t) : {x = y} + {x <> y}` Decide the equality of two strings.
* `eqb (x y : t) : bool` Test if two strings are equal.
  * `eqb_implies_eq : forall (x y : t), eqb x y = true -> x = y`
  * `eqb_same_is_eq : forall (x : t), eqb x x = true`
* `is_ascii (s : t) : bool` Test if the string contains only ASCII characters.
* `is_empty (s : t) : bool` Test if the string is empty.
* `join (separator : t) (l : list t) : t` Concatenate the list of strings `l` with the separator `separator`.
* `of_n (base : N) (digits : nat) (n : N) : t` Convert an integer to a string in base `base` with up to `digits` digits.
* `of_nat (base : nat) (H : 1 < base) (n : nat) : t` Convert an integer to a string in base `base`.
* `of_nat_2 (n : nat) : t` Convert an integer to a string in base 2.
* `of_nat_8 (n : nat) : t` Convert an integer to a string in base 8.
* `of_nat_10 (n : nat) : t` Convert an integer to a string in base 10.
* `of_nat_16 (n : nat) : t` Convert an integer to a string in base 16.
* `of_string (s : String.string) : t` Import a standard string. See the alias `s`.
* `repeat (s : t) (n : nat) : t` Repeat a string `n` times.
* `s (s : String.string) : t` Alias for `of_string`.
* `split (s : t) (c : ascii) : list t` Split a string at each occurrence of a given character. 
* `split_limit (s : t) (c : ascii) (limit : nat) : list t` Split a string at each occurrence of a given character in a list of up to [limit] elements.
* `t : Set := list Ascii.ascii` A string is a list of characters.
* `to_string (s : t) : String.string` Export to a standard string.
* `trim (s : t) : t` Remove white spaces at the beginning and the end of a string (spaces, \t, \n, \v, \f or \r).
* `trim_head (s : t) : t` Remove white spaces at the beginning of a string (spaces, \t, \n, \v, \f or \r).
* `trim_tail (s : t) : t` Remove white spaces at the end of a string (spaces, \t, \n, \v, \f or \r).
* `up_case (s : t) : t` Replace lowercase letters by uppercase ones (only characters from a to z are affected).

### Char
* `Char.compare (x y : Ascii.ascii) : comparison` Total order on characters.
  * `Char.compare_implies_eq : forall (x y : Ascii.ascii), compare x y = Eq -> x = y`
  * `Char.compare_same_is_eq : forall (x : Ascii.ascii), compare x x = Eq`
* `Char.digit (n : N) : Ascii.ascii` The character of a digit (0, 1, ..., 9, A, B, ...).
* `Char.down_case (c : Ascii.ascii) : Ascii.ascii` Replace uppercase letters by lowercase ones (only characters from a to z are affected).
* `Char.eqb (x y : Ascii.ascii) : bool` Test if two characters are equal.
* `Char.is_ascii (c : Ascii.ascii) : bool` Test if the character is in the ASCII range.
* `Char.is_white_space (c : Ascii.ascii) : bool` Test if the character is a white space (space, \t, \n, \v, \f or \r).
* `Char.up_case (c : Ascii.ascii) : Ascii.ascii` Replace lowercase letters by uppercase ones (only characters from a to z are affected).

Special characters:

command  | character
---------|----------
`Char.a` | bell
`Char.b` | backspace
`Char.t` | horizontal tabulation
`Char.n` | line feed
`Char.v` | vertical tabulation
`Char.f` | form feed
`Char.r` | carriage return
`Char.e` | escape
