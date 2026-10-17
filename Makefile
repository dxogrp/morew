BLUE := \033[36m
BOLD := \033[1m
RESET := \033[0m

LEANCHECK := LEAN_NUM_THREADS=1 lake env leanchecker PTran PTranTest

.DEFAULT_GOAL := help

.PHONY: update
update: ## update Lean dependencies and the package manifest
	@printf "$(BLUE)Updating Lean dependencies...$(RESET)\n"
	@lake update

.PHONY: imports
imports: ## synchronize generated root import aggregators
	@printf "$(BLUE)Synchronizing aggregate imports...$(RESET)\n"
	@status=0; lake exe mk_all || status=$$?; \
		if [ "$$status" -gt 125 ]; then exit "$$status"; fi; \
		lake exe mk_all --check

.PHONY: check-imports
check-imports: ## verify root import aggregators without changing them
	@printf "$(BLUE)Checking aggregate imports...$(RESET)\n"
	@lake exe mk_all --check

.PHONY: build
build: imports ## synchronize imports and build all Lean libraries warning-free
	@printf "$(BLUE)Building Lean libraries...$(RESET)\n"
	@lake build --wfail

.PHONY: lint
lint: build ## build and lint the shipped PTran library
	@printf "$(BLUE)Checking the lint driver configuration...$(RESET)\n"
	@lake check-lint
	@printf "$(BLUE)Linting PTran...$(RESET)\n"
	@lake lint

.PHONY: check-kernel
check-kernel: build ## build and kernel-check all compiled PTran modules
	@printf "$(BLUE)Kernel-checking compiled modules...$(RESET)\n"
	@$(LEANCHECK)

.PHONY: check
check: lint ## run the complete local development validation sequence
	@printf "$(BLUE)Kernel-checking compiled modules...$(RESET)\n"
	@$(LEANCHECK)

.PHONY: clean
clean: ## remove only PTran build artifacts
	@printf "$(BLUE)Cleaning PTran build artifacts...$(RESET)\n"
	@lake clean ptran

.PHONY: help
help: ## display this help message
	@printf "$(BOLD)Usage:$(RESET)\n"
	@printf "  make $(BLUE)<target>$(RESET)\n\n"
	@printf "$(BOLD)Targets:$(RESET)\n"
	@awk 'BEGIN {FS = ":.*##"; printf ""} /^[a-zA-Z_-]+:.*?##/ { printf "  $(BLUE)%-15s$(RESET) %s\n", $$1, $$2 }' $(MAKEFILE_LIST)
