FROM ubuntu:14.10
MAINTAINER Guillaume Claret

RUN apt-get update && apt-get upgrade -y
RUN apt-get install -y gcc make git
RUN apt-get install -y curl ocaml

# OPAM from the sources
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
RUN opam install -y coq.dev

# Tools
RUN apt-get install -y inotify-tools

# Compile
ADD . /root/coq-list-string
WORKDIR /root/coq-list-string
CMD eval `opam config env`; ./configure.sh && while inotifywait *.v; do make; done
