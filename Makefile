coqc     := coqc -noglob
coqfiles := $(shell find src -name \*.v)
allfiles := $(coqfiles) $(shell find src -name \*.hs)

default: $(allfiles)
	make build/Makefile.coq
	cd build; make OPT=-dont-load-proofs -f Makefile.coq Main.vo

build/Makefile.coq: $(coqfiles)
	mkdir -p build
	rm -f build/*.v
	rm -f build/*.d
	cd build; ln -s ../src/*.v .
	cd build; coq_makefile *.v > Makefile.coq

clean:
	rm -rf build
