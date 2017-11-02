
.PHONY: main clean

build:
	cp ../coq/build/bgpv.rkt main/
	sed -i.bak "s/(lambda  (_) (assert false))/symbolic-void/" main/bgpv.rkt
	sed -i.bak "s/(lambdas (s t v) (define-symbolic\\* b boolean?) (if b (s v) (t v)))/symbolic-boolean/" main/bgpv.rkt
	rm main/bgpv.rkt.bak
	cp ../coq/build/bgpv-core.rkt main/
	cp main/util/extraction.rkt main/util/extraction-racket.rkt
	sed -i.bak "s/#lang LANGUAGE/#lang racket/g" main/util/extraction-racket.rkt
	rm main/util/extraction-racket.rkt.bak
	cp main/util/extraction.rkt main/util/extraction-rosette.rkt
	sed -i.bak "s/#lang LANGUAGE/#lang s-exp rosette/g" main/util/extraction-rosette.rkt
	rm main/util/extraction-rosette.rkt.bak
	raco make main/bagpipe.rkt

clean:
	find /bagpipe/src/bagpipe/racket -name compiled -type d -exec rm -r {} +

