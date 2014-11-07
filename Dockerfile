FROM ubuntu:14.10
MAINTAINER Guillaume Claret

RUN apt-get update && apt-get upgrade -y
RUN apt-get install -y gcc make git
RUN apt-get install -y curl m4 ruby
RUN apt-get install -y aspcud
RUN apt-get install -y ocaml-nox

# OPAM
WORKDIR /root
RUN curl -L https://github.com/ocaml/opam/archive/1.2.0.tar.gz |tar -xz
WORKDIR opam-1.2.0
RUN ./configure
RUN make lib-ext
RUN make
RUN make install

# Initialize OPAM
RUN opam init
ENV OPAMJOBS 4

# Coq
RUN opam repo add coqs https://github.com/coq/repo-coqs.git
RUN opam install -y coq.8.4.5

# Coq repositories
RUN opam repo add coq-stable https://github.com/coq/repo-stable.git
RUN opam repo add coq-testing https://github.com/coq/repo-testing.git
RUN opam repo add coq-unstable https://github.com/coq/repo-unstable.git

# Dependencies
RUN opam install -y coq:error-handlers coq:list-plus

# Compile
ADD . /root/coq-list-string
WORKDIR /root/coq-list-string
RUN eval `opam config env`; ruby pp.rb && ./configure.sh && make
