FROM ubuntu:26.04

RUN apt-get update
RUN apt-get install -y autoconf graphviz libgmp-dev pkg-config zlib1g-dev
RUN apt-get install -y git opam

# Init opam without creating any switch
RUN opam init --bare --disable-sandboxing
RUN opam update -y

WORKDIR /seal

# The build context is the repository root
COPY . .
ENTRYPOINT ["./utils/run_build.sh"]
