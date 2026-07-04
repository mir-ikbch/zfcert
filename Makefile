.PHONY: all coq extract clean clean-extract

COQC_ENV = env -u COQLIB -u COQBIN -u COQTOP -u COQSOURCELIB -u COQSOURCEBIN
COQC = $(COQC_ENV) coqc -Q coq ZFCert

all: coq

coq:
	$(COQC) coq/FOL.v
	$(COQC) coq/ZFC.v
	$(COQC) coq/ProofState.v
	$(COQC) coq/TacticCompleteness.v
	$(COQC) coq/Audit.v

extract: coq
	$(COQC) coq/ExtractProofState.v

clean:
	rm -f coq/*.vo coq/*.vos coq/*.vok coq/*.glob coq/.*.aux

clean-extract:
	rm -f extracted/proof_state.ml extracted/proof_state.mli
