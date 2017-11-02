.PHONY: build

build: 
	cd /bagpipe/src/bagpipe/hs/; cabal install --enable-tests
	cd /bagpipe/src/bagpipe/coq/; make bagpipe
	cd /bagpipe/src/bagpipe/racket; make build


