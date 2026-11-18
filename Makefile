BLUE := \033[36m
BOLD := \033[1m
RESET := \033[0m

.DEFAULT_GOAL := help

.PHONY: cache
cache: ## download precompiled Mathlib files for the current dependencies
	@printf "$(BLUE)Downloading Mathlib build cache...$(RESET)\n"
	@lake exe cache get

.PHONY: update
update: ## update Lean dependencies and the package manifest
	@printf "$(BLUE)Updating Lean dependencies...$(RESET)\n"
	@lake update

.PHONY: imports
imports: ## synchronize generated root import aggregators
	@printf "$(BLUE)Synchronizing aggregate imports...$(RESET)\n"
	@for lib in Morew MorewTest Examples; do \
		status=0; lake exe mk_all --module --lib "$$lib" || status=$$?; \
		if [ "$$status" -gt 125 ]; then exit "$$status"; fi; \
		lake exe mk_all --module --check --lib "$$lib" || exit $$?; \
	 done

.PHONY: check-imports
check-imports: ## verify root import aggregators without changing them
	@printf "$(BLUE)Checking aggregate imports...$(RESET)\n"
	@for lib in Morew MorewTest Examples; do \
		lake exe mk_all --module --check --lib "$$lib" || exit $$?; \
	 done

.PHONY: build
build: imports ## synchronize imports and build all Lean libraries warning-free
	@printf "$(BLUE)Building Lean libraries...$(RESET)\n"
	@lake build --wfail

.PHONY: lint
lint: build ## build and lint the shipped Morew library
	@printf "$(BLUE)Checking the lint driver configuration...$(RESET)\n"
	@lake check-lint
	@printf "$(BLUE)Linting Morew...$(RESET)\n"
	@lake lint

.PHONY: check-kernel
# Replay all project roots and shared dependencies once in an empty kernel environment.
check-kernel: build ## build and kernel-check the library, tests, and examples
	@lake build --wfail KernelCheck
	@printf "$(BLUE)Kernel-checking compiled modules...$(RESET)\n"
	@LEAN_NUM_THREADS=1 lake env leanchecker --fresh KernelCheck

.PHONY: check
check: lint check-kernel ## run the local Lean build, lint, and kernel checks

.PHONY: docs
docs: ## build the documentation guide, examples, and API reference
	@./scripts/build_docs.sh

.PHONY: docs-update
docs-update: ## update the guide and examples in the existing preview
	@./scripts/build_docs.sh --update

.PHONY: preview
preview: ## preview generated documentation at http://127.0.0.1:8000
	@python3 -m http.server --bind 127.0.0.1 --directory build/docs 8000

.PHONY: clean
clean: ## remove only Morew build artifacts
	@printf "$(BLUE)Cleaning Morew build artifacts...$(RESET)\n"
	@lake clean morew

.PHONY: help
help: ## display this help message
	@printf "$(BOLD)Usage:$(RESET)\n"
	@printf "  make $(BLUE)<target>$(RESET)\n\n"
	@printf "$(BOLD)Targets:$(RESET)\n"
	@awk 'BEGIN {FS = ":.*##"; printf ""} /^[a-zA-Z_-]+:.*?##/ { printf "  $(BLUE)%-15s$(RESET) %s\n", $$1, $$2 }' $(MAKEFILE_LIST)
