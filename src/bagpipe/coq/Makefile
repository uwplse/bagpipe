NAME=Bagpipe

BUILD=build

CP=cp
UNAME := $(shell uname -s)
ifeq ($(UNAME),Darwin)
	CP=gcp
endif

build= \
  mkdir $(BUILD) 2> /dev/null || true; \
  find $(1) -path ./$(BUILD) -prune -o -name '*.v' -print | xargs $(CP) -a --parents -t $(BUILD); \
  cd $(BUILD); find . -name '*.v' | xargs coq_makefile -R . $(NAME) -o Makefile; cd -; \
  make -j4 -C$(BUILD)

.PHONY: main bagpipe clean

main:
	$(call build,Main)

gao-rexford: main
	$(call build,GaoRexford)

bagpipe: main
	$(call build,Bagpipe)
	cp Bagpipe/header-core.rkt $(BUILD)/bgpv-core.rkt
	tail -n +4 $(BUILD)/bgpv-core.scm >> $(BUILD)/bgpv-core.rkt
	sed -i.bak "s/(define __ (lambda (_) __))/(define __ 'unused)/g" $(BUILD)/bgpv-core.rkt
	sed -i.bak 's/(error "AXIOM TO BE REALIZED")/__/g' $(BUILD)/bgpv-core.rkt
	cp Bagpipe/header.rkt $(BUILD)/bgpv.rkt
	tail -n +4 $(BUILD)/bgpv.scm >> $(BUILD)/bgpv.rkt
	sed -i.bak "s/(define __ (lambda (_) __))/(define __ 'unused)/g" $(BUILD)/bgpv.rkt
	sed -i.bak 's/(error "AXIOM TO BE REALIZED")/__/g' $(BUILD)/bgpv.rkt

clean:
	rm -r $(BUILD)

