.PHONY: all clean serve

COQDOC_AUTO=coqdoc.css

FILES=index
FILES_HTML=$(addsuffix .html,$(FILES))

all: $(FILES_HTML)

%.html: %.v %.glob
	./jscoqdoc $<

%.glob: %.v
	coqc $<

clean:
	rm -f *.vo *.vok .*.aux *.glob *.vos $(FILES_HTML) $(COQDOC_AUTO)

node_modules: package.json package-lock.json
	npm i

serve: node_modules
	./node_modules/.bin/http-server .
