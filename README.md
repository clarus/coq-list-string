# coq-list-string
Strings implemented as lists. Finally.

## Install
With OPAM add the Coq repository:

    opam repo add coq https://github.com/coq/opam-coq-repo.git

and run:

    opam install coq-list-string

From the sources do a classic:

    ./configure.sh
    make
    make install

## Use
Add:

    Require Import ListString.ListString.

at the beginning of your source files. The library will be available under the `ListString` module. It defines the type `ListString.t` of strings encoded as lists of ASCII 8-bits characters. To define a string you can either define a list:

    ["h"; "e"; "l"; "l"; "o"]

or import a Coq `string` using the string notation:

    ListString.s "hello"

## Reference
TODO