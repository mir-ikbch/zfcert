.PHONY: all coq extract wasm clean clean-extract

COQC_ENV = env -u COQLIB -u COQBIN -u COQTOP -u COQSOURCELIB -u COQSOURCEBIN
COQC = $(COQC_ENV) coqc -Q coq ZFCert

all: coq

coq:
	$(COQC) coq/FOL.v
	$(COQC) coq/ZFC.v
	$(COQC) coq/ProofState.v
	$(COQC) coq/TacticCompleteness.v
	$(COQC) coq/NamedProofState.v
	$(COQC) coq/NamedCommands.v
	$(COQC) coq/CertifiedSession.v
	$(COQC) coq/GlobalEnvironment.v
	$(COQC) coq/Audit.v

extract: coq
	$(COQC) coq/ExtractProofState.v

wasm:
	dune build wasm/main.bc.wasm.js
	dune build wasm/main_js.bc.js
	mkdir -p web/wasm
	chmod -R u+w web/wasm
	cp -f _build/default/wasm/main.bc.wasm.js web/wasm/
	cp -f _build/default/wasm/main_js.bc.js web/wasm/
	cp -Rf _build/default/wasm/main.bc.wasm.assets web/wasm/

clean:
	rm -f coq/*.vo coq/*.vos coq/*.vok coq/*.glob coq/.*.aux

clean-extract:
	rm -f extracted/proof_state.ml extracted/proof_state.mli
