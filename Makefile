.PHONY: setup test verify python-test

setup:
	./scripts/setup.sh

test:
	./scripts/test_all.sh

verify:
	./scripts/verify_layer.sh all

python-test:
	uv sync --locked
	uv run python scripts/test_solidity_to_yul_lean.py -v
