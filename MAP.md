# Map of the Bagpipe Codebase
This is a map for tracing the execution of the Bagpipe tool and a high-level guide for finding implementations of different functionality.

#### Where execution starts: /src/bagpipe/python/bagpipe
Calling this Python file with "verify" as the first arg in turn invokes      
/src/bagpipe/racket/main/bagpipe.rkt

#### Interface to extracted Coq code: /src/bagpipe/racket/main/bagpipe.rkt
The function "verify" is what actually invokes the extracted Coq code (provided
as the function "bgpv" in /src/bagpipe/racket/main/bgpv.rkt after running make, 
see below). Note that some functions in this file like unpack-counter-example 
operate directly on extracted Coq data structures, so if the constructors seem 
out of place, find the Coq code dealing with the same data structures. The key 
logic in "verify": "load-as" reads in the AS config (see "setup.rkt" below), 
"load-prop" passes args to the AS's setup logic ("setup.rkt"), "load-driver" 
loads the AS's setup logic ("setup.rkt"), then it prints out the topology of the 
AS (assuming internal routers in a full mesh configuration), then it invokes
"bgpv" with the loaded AS, driver, and props and parses the results (a list of 
counterexamples if any exist).

#### Utility functions: /src/bagpipe/racket/main/util/util.rkt and extraction.rkt
These files (and others in their directory, but these are very common) define 
certain basic functions for processing extracted Coq code, such as the "@" macro
(curried application), a match syntax similar to Coq's matching, and 
"lambdas" (curried lambda). Note that the Makefile in /src/bagpipe/racket makes 
two copies of extraction.rkt: one in #lang racket (extraction-racket.rkt) and 
one in #lang rosette  (extraction-rosette.rkt); these do not differ in their 
contents, but the extra version allows the functions to cleanly interoperate 
with Rosette.

#### Reading in an AS: /src/bagpipe/racket/main/setup.rkt
This file has some utility functions that interact with the "setup" argument 
passed to the Bagpipe tool at the top level; most of the functionality is 
delegated to the setup. "load-as" loads the "setup.rkt" *of the passed setup* 
(not /src/bagpipe/racket/main/setup.rkt), enters it into the current namespace 
(thus allowing the user's setup.rkt to use various utility functions in /src/
bagpipe/racket/main/config.rkt or /src/bagpipe/racket/main/util/extraction.rkt),
and evaluates the user's "as" function using the passed args. Similarly, 
"load-driver" calls the user's "driver" function defined in their setup.rkt and 
"load-prop" does the same with the user's "policy" function (though its return 
value appears to just be the contents of setup.rkt?) See the setup.rkt in the
example.tar on the Bagpipe website for an example of how the user's functions
should look and what they return (this will be discussed with Extract.v below).

#### Representing and processing an AS: /src/bagpipe/racket/main/config.rkt
This file's functions are provided to users for writing a setup.rkt in their 
configs, facilitating the parsing of router configs. The function as-from-configs
takes a config language (either "juniper" or "cisco") and a list of router 
config file names and parses the files into an AS, delegating this to the 
juniper-as-from-configs and cisco-as-from-configs functions depending on the 
configuration language (in juniper/juniper.rkt and cisco/cisco.rkt, 
respectively). Given this AS representation, "dispatch" branches on the 
representation's language. The other functions in the file perform high-level
operations on the configs, independently of config language: "as-denote-import"
and "as-denote-export" return how the AS would modify an import or export 
announcement (or if it drops the announcement), "as-environment" returns an AS 
environment, "as-internal-routers" returns a list of internal routers (IP 
addresses), and "as-router-external-neighbors" returns the list of external 
neighbors to an internal router (the router and the neighbors are given by their 
IP addresses). As this file provides a high-level API for interacting with AS 
representations, I will not go into much detail on how specifically the files in 
juniper/ and cisco/ do their parsing except to say that the parsers for Juniper 
and Cisco config files are written in Haskell in the /src/bagpipe/hs/ directory.
The actual representation of an AS is as a list of S-expressions where each
S-expression represents a config file's commands (these are built up by the 
Haskell parsers).

#### Specifying network properties: /src/bagpipe/racket/main/network/network.rkt et al
These files define functions for processing IP addresses, testing properties of 
routers in an AS, or testing properties of BGP announcements. They should be used
to specify a policy in the user-defined setup.rkt for their config files (a 
policy should be a function that operates on the representation of the AS and
evaluates to true iff all desired properties for the AS are satisfied), see 
example.tar on the Bagpipe website for examples of these functions' use.

#### Extracting Coq code: /src/bagpipe/coq/Bagpipe/Extract.v
This file assembles together all the main Bagpipe logic defined in coq (mostly 
in coq/Main/BGPV.v) and defines how it should be extracted to Racket. Be certain 
to see /src/bagpipe/coq/Makefile, as it shows the different steps of the 
extraction process: first we use Coq's native extraction to Scheme, then change 
it to a Racket file (similar-enough languages!), then append /src/bagpipe/coq/
Bagpipe/header.rkt (or header-core.rkt) to the front of the file to produce the 
complete Racket file, ultimately in /src/racket/racket/main/bgpv.rkt and 
bgpv-core.rkt (bgpv.rkt uses header.rkt and bgpv-core.rkt uses header-core.rkt). 
Of note in Extract.v is the definition of the function "bgpv," which takes an AS,
an execution mode ("all" meaning to check the policy on all announcements, 
"import" to check import announcements only, "export" to check export 
announcements only, and "preference" to check route preference announcements 
only), and a query (policy to check) and runs the core Bagpipe logic under those 
settings. Note the various "Extract Constant"  commands, which give direct 
Rosette definitions to certain properties in order to use symbolic variables or 
otherwise manually override behavior. Note that even though the definition of 
"bgpv" does not list a query variable, it still takes one, as the 
"elimExecutionMode" function returns *partially applied* functions that 
still need to take a query (policy). Hence, this is why the call to bgpv in /src/
bagpipe/racket/main/bagpipe.rkt passes three arguments, thanks to currying.

#### Beyond this: /src/bagpipe/coq/Main/BGPV.v
/src/bagpipe/coq/Main/BGPV.v is where the heart of Bagpipe resides, 
the verification logic described in the paper. Perhaps information about the 
Coq-internal architecture will be added here but this so far describes how 
configs are ultimately passed to the core BGP verification logic in Coq.

