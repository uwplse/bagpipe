COQINCLUDES=-R ../build Bagpipe -R . Bagpipe
COQC=coqc $(COQINCLUDES)
COQTOP=coqtop $(COQINCLUDES) -batch -load-vernac-source
RM=rm -f

default: TestCBGP

ExtractPrelude.vo : ExtractPrelude.v
	$(COQC) ExtractPrelude.v

MessageHandling.hs : ExtractPrelude.vo Extract.v
	$(COQTOP) Extract.v

TestCBGP : MessageHandling.hs
	stack build
	stack install --local-bin-path .

clean :
	stack clean
	$(RM) TestCBGP
	$(RM) MessageHandling.hs
	$(RM) *.vo
	$(RM) *.aux
	$(RM) *.glob

.PHONY : TestCBGP default clean
