all:
	@dune build _build/default/flat.install --display short
.PHONY: all

install:
	@dune install
.PHONY: install

uninstall:
	@dune uninstall
.PHONY: uninstall

doc:
	ROOT=`pwd` dune build theories/flat.html/
	rm -rf doc/
	cp -R _build/default/theories/flat.html/ doc/
	cp -R coqdocjs/resources/ doc/
.PHONY: doc

clean:
	@dune clean
	rm -rf doc/
.PHONY: clean