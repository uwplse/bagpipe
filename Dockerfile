FROM ubuntu:14.04.2
MAINTAINER Konstantin Weitz <konstantin.weitz@gmail.com>

# install basic tools
RUN apt-get update && \
    apt-get install -y \
      binutils \
      curl \
      fish \
      git \
      g++ \
      make \
      python \
      python-pip \
      vim \
      unzip \
      wget

# install z3
RUN git clone https://github.com/Z3Prover/z3.git && \
    cd z3; python scripts/mk_make.py && \
           cd build; make; make install

# install racket
RUN wget http://mirror.racket-lang.org/installers/6.6/racket-6.6-x86_64-linux.sh -O install.sh && \
    chmod +x install.sh && \
    ./install.sh --in-place --create-links /usr --dest /usr/racket && \
    rm install.sh

# install rosette
RUN apt-get update && \
    apt-get install -y \
      libcairo2-dev \
      libpango1.0-dev \
      libjpeg-dev && \
    git clone https://github.com/emina/rosette.git && \
    cd rosette; git checkout 2.2 && \
                raco pkg install

# install opam
RUN wget https://raw.github.com/ocaml/opam/master/shell/opam_installer.sh -O - | sh -s /usr/local/bin && \
    opam init -n --comp=4.01.0
ENV PATH "/root/.opam/4.01.0/bin":$PATH

# install coq
RUN opam install coq.8.5.2

# install space-search
RUN opam update && opam install space-search.0.9.1

# install sshd
RUN apt-get update; \
    apt-get install -y \
      openssh-server && \
    ssh-keygen -q -t rsa -N '' -f /root/.ssh/id_rsa && \
    cp /root/.ssh/id_rsa.pub /root/.ssh/authorized_keys && \
    echo 'Host *' >> /root/.ssh/config && \
    echo '    StrictHostKeyChecking no' >> /root/.ssh/config && \
    echo '    Port 2222' >> /root/.ssh/config && \
    sed -i.bak 's/Port 22/Port 2222/' /etc/ssh/sshd_config

# enable rosette debugging
RUN cd rosette && \
# debug errors during symbolic execution
#   sed -i "s/;(printf/(printf/g" rosette/base/core/effects.rkt && \
# debug formula sent to solver
    sed -i "s/;(fprintf/(fprintf/g" rosette/solver/smt/smtlib2.rkt && \
    raco pkg remove rosette && \
    raco pkg install

ENV BAGPIPE /bagpipe
EXPOSE 2222
EXPOSE 1234-1298
ENTRYPOINT ["bagpipe"]
ENV PATH /bagpipe/src/bagpipe/python:$PATH

# install haskell
RUN apt-get update && \
    apt-get install -y \
      haskell-platform
ADD src/bagpipe/hs/bagpipe.cabal /bagpipe/src/bagpipe/hs/
RUN cd /bagpipe/src/bagpipe/hs; cabal update; cabal install Cabal; cabal install --only-dependencies

build bagpipe
ADD . /bagpipe
RUN make -C /bagpipe
# test bagpipe
# RUN cd /bagpipe/src/bagpipe/racket; ./run-tests

