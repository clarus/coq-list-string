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

    Require Import ListString.ListString.

at the beginning of your source files. The library will be available under the `ListString` module. It defines the type `ListString.t` of strings encoded as lists of ASCII 8-bits characters. To define a string you can either define a list:

    ["h"; "e"; "l"; "l"; "o"] : ListString.t

or import a Coq `string` using the string notation:

    ListString.s "hello" : ListString.t

## Reference
* `Ascii.compare (x y : Ascii.ascii) : comparison`
* `Ascii.compare_implies_eq : forall (x y : Ascii.ascii), compare x y = Eq -> x = y`
* `Ascii.compare_same_is_eq : forall (x : Ascii.ascii), compare x x = Eq`
* `Ascii.eqb (x y : Ascii.ascii) : bool`
* `compare (x y : t) : comparison`
* `compare_same_is_eq : forall (x : t), compare x x = Eq`
* `compare_implies_eq : forall (x y : t), compare x y = Eq -> x = y`
* `eqb (x y : t) : bool`
* `eqb_implies_eq : forall (x y : t), eqb x y = true -> x = y`
* `eqb_same_is_eq : forall (x : t), eqb x x = true`
* `eq_dec (x y : t) : {x = y} + {x <> y}`
* `of_string (s : String.string) : t`
* `to_string (s : t) : String.string`
* `s (s : String.string) : t`
* `split (s : t) (c : ascii) : list t`
* `split_limit (s : t) (c : ascii) (limit : nat) : list t`
* `t : Set := list Ascii.ascii`