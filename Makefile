# Common tasks; `make help` lists them.
PYTHON ?= python3
# tests run in parallel: one job per core unless JOBS is given (make test JOBS=2)
JOBS   ?= $(shell nproc 2>/dev/null || getconf _NPROCESSORS_ONLN 2>/dev/null || echo 4)

.PHONY: help check unit test test-all update-logs package api

help:  ## list the targets
	@grep -E '^[a-z-]+:.*## ' $(MAKEFILE_LIST) | sed 's/:.*## /\t/'

check:  ## every script has its committed logs, free of Magma errors, and the package and the API reference are up to date (no Magma needed)
	$(PYTHON) tests/check_logs.py
	$(PYTHON) tools/make_package.py --check
	$(PYTHON) tools/make_api.py --check

unit:  ## unit tests of the test tools (Python, seconds)
	$(PYTHON) -m unittest discover -s tests

test:  ## Magma regression tests, fast tier (about 14 minutes of CPU time)
	$(PYTHON) tests/regression.py --tier fast -j $(JOBS)

test-all:  ## all Magma regression tests, including the two Example 8.4 runs
	$(PYTHON) tests/regression.py --tier all -j $(JOBS)

package:  ## rebuild the Magma package package/ColemanIntegralsLocalFields.m from the library files
	$(PYTHON) tools/make_package.py

api:  ## rebuild the API reference docs/API.md from the comments of the library files
	$(PYTHON) tools/make_api.py

update-logs:  ## re-run every script and overwrite the committed logs
	$(PYTHON) tests/regression.py --tier all -j $(JOBS) --update
