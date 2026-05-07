.PHONY: build challenge solution audit no-sorry imports comparator

build:
	lake build AdmissibleCarry

challenge:
	lake build Challenge

solution:
	lake build Solution

audit:
	scripts/audit_sorries.sh .
	tools/check_no_sorry.sh
	scripts/audit_imports.sh .

no-sorry:
	tools/check_no_sorry.sh

imports:
	scripts/audit_imports.sh .

comparator:
	lake env comparator comparator.json
