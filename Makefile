ISABELLE ?= isabelle

.PHONY: all check clean

all: .build/ready

.build/ready: ROOT $(wildcard src/*.thy tests/*.thy) cli/driver.ML Makefile
	@test "$$('$(ISABELLE)' version)" = Isabelle2026 || { printf '%s\n' 'span requires Isabelle2026' >&2; exit 1; }
	"$(ISABELLE)" build -D . -j 1 -o threads=1 -o parallel_proofs=0
	"$(ISABELLE)" export -n -d . -O .build -x 'Span.Export:code/span.ML' Span
	SPAN_ROOT="$(CURDIR)" "$$('$(ISABELLE)' getenv -b POLYML_HOME)/$$('$(ISABELLE)' getenv -b ISABELLE_PLATFORM64)/polyc" -o .build/span cli/driver.ML
	@touch $@

check: all
	python3 tests/cli.py

clean:
	rm -rf .build
