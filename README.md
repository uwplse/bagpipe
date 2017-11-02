Bagpipe
================

### Getting Started with Bagpipe

Bagpipe is a tool which enables an ISP to express its BGP policy in a
domain-specific specification language and verify that its router configurations
implement this policy.

This README provides a quick start guide for Bagpipe, a more in depth discussion
can be found [here](http://konne.me/bagpipe).

Checkout Bagpipe from github:

    git clone --recursive git@github.com:uwplse/bagpipe.git
 
[Docker][docker] is the most reliable way to build Bagpipe. To build
Bagpipe and all its dependencies run (running this command for the first
time may take an hour) in the `bagpipe` directory:

    docker build -t bagpipe .

[docker]: https://docs.docker.com/engine/installation/

### Developing Bagpipe

You can also use Docker to start a Bagpipe development environment that has
all the right dependencies setup: 

    docker rm -f bagpipe; docker run --name bagpipe --entrypoint /bin/bash -v $(pwd):/bagpipe -ti bagpipe

Running the above command starts a shell in the development environment. You can
build the Bagpipe project with:

    make -C /bagpipe

From another terminal, you can connect to the development environment with your
local emacs installation:

    emacs /docker:bagpipe:/bagpipe/src/bagpipe/coq/Main/BGPSpec.v 

If your docker instance runs on another machine, you can connect to it with:

    emacs "/ssh:user@machine|docker:bagpipe:/bagpipe/src/bagpipe/coq/Main/BGPSpec.v"

Make sure your emacs has `ProofGeneral` and `docker-tramp` installed, and 
`enable-remote-dir-locals` must be set.

### Publishing Bagpipe

To push bagpipe to DockerHub run:

    docker login
    docker push konne/bagpipe-private

The name of your local image must match the name that you wish to push.
You can get the image back with

    docker pull

