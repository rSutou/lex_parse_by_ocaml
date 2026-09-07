test: 
	dune clean
	dune build
	dune exec LangBuilder bin/sampleLang.lang
	cp Lang.ml ../lex_parse/bin/Lang.ml
	cd ../lex_parse
	dune build