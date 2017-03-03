libs: Axioms.v Defns.v Lemmas.v
	coqc Axioms.v && coqc Defns.v && coqc Lemmas.v

clean:
	rm *.glob *.vo
