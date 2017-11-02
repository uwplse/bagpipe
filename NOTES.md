Computation
-----------

The `compute` tactic is nice, because it is conceptually very simple. But there are several downsides to `compute`.

- `compute` unfolds definitions even if we don't want to depend on the definition, e.g. because the definition's type is sufficient. This problem might indicate that a problem can be generalized by hiding definitions using techniques such as ADTs. The problem can also be circumvented using the `generalize` tactic or the `Opaque` command.

- `compute` unfolds definitions (that we want to depend on eventually) before we actually need them (because we first have to deal with recursion/pattern matching). For example:

    Goal forall n, n + 0 = 0 + n.
      intros.
      compute in *.   (* unfolding + is unnecessary *)
      Undo.
      intros. 
      induction n.
      + compute in *.
        reflexivity.
      + compute in *.   (* unfolding + the second time is unnecessary *)
        rewrite IHn.
        reflexivity.
    Qed.

The `cbv` tactic tries to avoid 




Overview
--------

### Running & Building

To run Bagpipe [see](http://konne.me/bagpipe).

To build Bagpipe, run:

    docker build -t bagpipe .
    cat example.tar | docker run -i bagpipe verify atla-no-sanity 

If you cannot run `docker` locally, install docker machine and run:

    docker-machine create -d virtualbox --virtualbox-memory 8192 --virtualbox-cpu-count 8 dev
    eval "$(docker-machine env dev)"

Debug with

    docker run -ti --entrypoint bash bagpipe

To create a cluster to run on, execute:

    ./cluster.py

To push bagpipe to DockerHub run:

    docker login
    docker push konne/bagpipe-private

The name of your local image must match the name that you wish to push.
You can get the image back with

    docker pull

### Policy Optimization Options.

We assume a set of routers $R$, and a set of neighbors for each router $r$ 
called $N_r$. 

The total number of neighbors is $|N| = \sum{r:R} |N_r|$
The number of incoming connections into a router $r$ is $|in_r| = |R|+|N_r|$.
The number of outgoing connections from a router $r$ is $|out_r| = |R|+|N_r|-1$.
The number of routings into a router $r$ is $|P_r| = |in_r| + \sum{r':R} |N_{r'}| = |in_r| + |N|$

The total number of paths to enumerate by Bagpipe depends on the mode that Bagpipe is operated in:

#### ribIn 

The total number of paths to enumerate is:

$\sum{r:R} |P_r|$
$= \sum{r:R} |R|+|N_r|+|N|$
$= |R|^2+|R||N|+|N|$

The number of paths is dominated by $O(|R|^2 + |R||N|)$.

e.g. Internet 2 has $|R|=10$ and $|N|=274|$ such that the total number of paths to enumerate equals $3,114$. This is well approximated by $|R||N| = 2,730$.

### ribOut

The total number of paths to enumerate is:

$\sum{r:R} |out_r| |P_r|$
$= \sum{r:R} (|R|+|N_r|-1) (|R|+|N|+|N_r|)$
$= \sum{r:R} (y+|N_r|) (x+|N_r|)$ where $x = |R|+|N|$ and $y = |R|-1$
$\le |R|xy + y|N| + x|N| + |N|^2$

The number of paths is dominated by $O(|R|^3 + |R|^2|N| + |N|^2)$.

For Internet2, I expect this to be about $|N|^2 = 74,529$

#### locRIB

The total number of paths to enumerate is:

$\sum{r:R} |P_r|^2$
$= \sum{r:R} (|R|+|N|+|N_r|)^2$
$= \sum{r:R} (x+|N_r|)^2$ where $x = |R|+|N|$
$= |R|x^2 + 2|N|x + \sum{r:R} |N_r|^2$
$\le |R|x^2 + 2|N|x + |N|^2$

The number of paths is dominated by $O(|R|^3 + |R|^2|N| + |R||N|^2)$.

For Internet2, I expect this to be about $|R||N|^2 = 745,290$

#### full

$\sum{r:R} |out_r| |P_r|^2$


More about Docker
-----------------

### Problem Introduction

Bagpipe has three essential challenges:

- I want to ship Bagpipe to users. This is hard because Bagpipe depends on Haskell, Racket, Rosette, and Z3. I cannot assume that any of my users (potentially network operators) has every used any of these rather niche technologies, and we depend on python and a bunch of libraries like dispy, and Java.

- I want to run Bagpipe on many machines. This is hard because it means I have to configure multiple machines to run my stuff. I also need automation that gets a newly booted computer into the right state. This is ok for AWS, but I also have machines run by my university that I would like to use for free along with AWS (I don't have root on these machines).

- I want reproducible results (both for the paper evaluation), and for users of the tool. My experience has shown that it is crucial for reproducibility to automate as much of the work-flow as possible.

The overall problem here is that there is a lot of _context_ that Bagpipe requires in order to run, and it's not clear how to describe precisely what this context is. I can try to do it in natural language, e.g. "install haskell before you run this", but there are many problem with this. How do you install haskell on your machine? which version? ... . There are also other problems, e.g. which OS version, what other applications are installed on the system, ...
I'm not a good enough of a writer to explain this all, also, there are so many things that could influence Bagpipe, e.g. other running processes, there is just no way I can figure out what kind of context is going to break my app. For large projects these contexts are usually figured out over time, as users complain about their system setup, and after a while you get all the people with the common architectures to complain about their lives to you. Once the context of my App is well defined, we can do _automation_.

How can I solve this? It turns out that the answer is Docker! 
The problem of having people get the context right, has essentially been reduced to installing and configuring Docker. The hope is that Docker is common enough, that people already know how to use it, or will learn something that will be useful throughout their entire life by learning about Docker. Also, because Docker is common, it is possible for people to send lots of money on automating tasks with Docker. E.g. Amazon supports them out of the box with [Amazon EC2 Container Service][ECS].

### Installing Docker

_Docker_ runs on all modern operating systems. For information on how to install it see the [Docker installation guide][DIG].
Don't worry, it'll be extreamly valueable for you to invest some time to learn how to install docker, it's awesome!
(On OSX I had a good experience running Kitematic, then opening the console.)
You should also install _docker compose_ describes [here][DC].

### Creating and Running Docker Images

We want to install our stuff. We are basing it on ubuntu. We can (but don't have to) download ubuntu with:

    docker pull ubuntu 

Turn out that Docker's ubuntu doesn't come with `wget` and the platform hasn't been around long enough to include `wget`. So let's create an image that include `wget`.

We write the following `Dockerfile` (the filename is literally that):

    FROM ubuntu
    RUN apt-get -y install wget

The we can build the new image using (`-t` specifies a tag, `.` is the directory of the docker file):

    docker build -t konne/ubuntu-wget .

We can check that the image was created with:

    docker images

We can now run the _image_ (create a container) with:

    docker run -i -t konne/ubuntu-wget

Inside the container we can run `wget` we see that the command is now actually installed:

    # wget --version
    GNU Wget 1.15 built on linux-gnu. 
    ...

We can check that this _container_ ran by running (`-a` means that exited containers are also shown):

    docker ps -a

### Pushing to DockerHub

You can push the image to the web, with:

    docker push konne/ubuntu-wget

Pushing is not perfect, because the docker file isn't online. A better way is to create a public git-hub repo and connect AutoBuild with the website.

### Linking Docker Images

This is great, we have setup a single process running on a single machine! One of the hip things these days is to use multiple machines to run a task, because one just ain't enough. To create a cluster of machines, we can define a `docker-compose.yml` file:

    client:
      image: ubuntu
      command: ["sh", "-c", "sleep 3; echo Test | nc server 8080"]
      links:
      - server
    server:
      image: ubuntu
      command: ["nc", "-l", "8080"]

Start it with

    docker-compose build
    docker-compose up

### Cloud

[Google's Containers] uses Kubernetes to get you running.

[GC]: https://cloud.google.com/compute/docs/containers



This [documentation][CLD] describes how to connect to all sorts of different providers. We connect to amazon like so:

    docker-machine create \
    --driver amazonec2 \
    --amazonec2-access-key <ACCESS-KEY> \
    --amazonec2-secret-key <SECRET-KEY> \
    --amazonec2-vpc-id     <VPC-ID> \
    ec2box




    parallel --no-notice docker-machine create \
    --driver amazonec2 \
    --amazonec2-access-key AKIAJC2SDMTURN72PATQ \
    --amazonec2-secret-key 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 \
    --amazonec2-vpc-id vpc-833b03eb \
    --amazonec2-subnet-id subnet-853b03ed \
    --amazonec2-region us-west-2 \
    --amazonec2-zone a \
    --amazonec2-instance-type c3.8xlarge \
    ::: bagpipe-{0,1,2,3,4,5,6,7}

    parallel --no-notice docker-machine create \
    --driver amazonec2 \
    --amazonec2-access-key AKIAJC2SDMTURN72PATQ \
    --amazonec2-secret-key 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 \
    --amazonec2-vpc-id vpc-833b03eb \
    --amazonec2-subnet-id subnet-853b03ed \
    --amazonec2-region us-west-2 \
    --amazonec2-zone a \
    --amazonec2-instance-type c3.8xlarge \
    ::: bagpipe-{0,1,2,3,4,5,6,7}

    docker-machine rm ec2box

### Running a virtual Docker machine on your Computer

What Kitematic does is run the following command:

    docker-machine create -d virtualbox dev    

Next run the following command in the terminal that you want to use:

    eval "$(docker-machine env dev)"



### Reflection

Given my background as a Programming Languages Researcher, it is hard for me not to look at this problem through a Programming Language lens. A large just of Programming Language Research is about _assigning meaning to programs_. 

Through this lens, the essential problem with Bagpipe is that given only its source code, it is unclear what it means to run Bagpipe. The things that the source code (i.e. the git repo) doesn't describe is the context of the application. E.g. one thing that is in the context are standard libraries. What does the following Python code mean, given that the standard library isn't part of the context?

    sorted([3, 2, 1])

Sorted could be any function. Another example is that I need to know that my code has to be run with python, but python is not in my repo, so this is really just a string.

Now it turns out that we can describe all this context decently with text, but text has many disadvantages:
- no automation
- ambiguity
- ...

Docker is a language that allows us to describe this context in a machine understandable way, and thus to assign meaning to our programs. The gap isn't fully closed, we still have to understand Docker (which is not in our repo), to assign meaning to our application. And while Docker might be more complex than other common ways to assign meaning, e.g. translate a program into math (see TaPL, 3.4 Semantic Styles), but its right in the sweet spot between supporting all existing technologies, and being easy to reason about.

There is also a question of assigning blame here. If you run a program with the "wrong" context (e.g. because you interpreted the ambiguities in the installation instructions different than the developer), you are usually to blame and might not even be able to open a bug report. If a docker container fails, its usually pretty clear that there is a bug in the software.

One potential problem with Docker is non-determinism (i.e. a program can run in many different ways given the same inputs). On the plus side, it is usually known by developers that a program must function correctly for-all non-deterministic choices made by the environment (again, this is not necessarily the case with context, people don't write software that runs on all possible contexts, e.g. most software will not run if you replace all functions in the stdlib with `id`). Thus, if a docker container breaks, it's the developer's fault.

A problem with non-determinism is that it's untestable. If your memcpy always allocates memory in the forward direction, it's impossible to test what will happen in the backward direction (you can use mocking or stuff like that though). Theorem proving might help here. 

This actually happened, and it killed a lot of applications. [Linus's PoV][MCP]here is that it's a bug to have changed the non-deterministic behavior.

Restricting non-deterministic behavior is tough though. There are instructions that do non-determinism, and if you have multiple threads the scheduler introduces non-determinism, and if you do IO its even more. NaCL has a good [summary of non-determinism][NACL]. If you want this additional level of guarantee and reproducibility, you might want to consider using NaCL.

I think it's OK to have non-determinism, and making it the developer's responsibility to run for-all possible non-deterministic choices! It's potentially a pain to debug, but that just means we need better tooling, e.g. a tool that traces all non-deterministic choices and then replays them.

Maven had a similar attempt, but they only closed to GAP down to having Java installed, and there were still many problems that Maven didn't address, like: what does my file system look like.

While they are awesome, I have had bad experiences with virtual machines:
- Size: VMs are huge (many GB). This means its practically impossible to put them in version control, which means that in the past I have had a horrible time dealing with different versions especially when working with collaborators. VMs are in a sense extremely well compressible. There are only a handful of commands executed to create them. A problem that I don't have the handful of commands but just the end result, is that it makes it very hard to change the VM. E.g. if I want to change the OS, it's not well documented which software I might want to install in the new OS.

[ECS]: http://aws.amazon.com/ecs/
[MCP]: https://sourceware.org/bugzilla/show_bug.cgi?id=12518
[NACL]: https://code.google.com/p/nativeclient/wiki/DeterministicExecution
[CLD]: https://docs.docker.com/machine/
