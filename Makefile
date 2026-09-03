.PHONY: build validate catalog check check-lean check-web serve browser-qa clean

PORT ?= 4173
URL ?= http://127.0.0.1:$(PORT)/

# Build the library as well as the executable. The executable's root (Leanproofs.Main) does
# not import Leanproofs.Catalog -- it reads the catalog out of the environment at runtime --
# so `lake build frontier` alone succeeds against stale oleans and the audit below would
# then validate a registry that no longer compiles.
build:
	lake build Leanproofs frontier

validate: build
	lake exe frontier validate

catalog: build
	lake exe frontier export web/data/catalog.json

# The full gate. Runs in CI; run it before pushing.
check: check-lean check-web

# Kernel audit plus the guarantee that the committed web catalog still matches the registry.
# The comparison is structural rather than byte-for-byte: pretty-printed Lean types move with
# the toolchain, so a mathlib bump should not fail the build over rendering churn.
check-lean: build
	lake exe frontier validate
	lake exe frontier export build/frontier.check.json
	python3 scripts/compare-catalog.py build/frontier.check.json web/data/catalog.json

# Syntax check, then drive the real page in a real browser if one is reachable.
check-web:
	node --check web/app.js
	node --check scripts/browser-qa.mjs
	$(MAKE) browser-qa

serve: catalog
	python3 -m http.server $(PORT) --bind 127.0.0.1 --directory web

# Serves the workspace on a throwaway port and drives it over the Chrome DevTools Protocol.
# Skips with a notice when no CCP endpoint is reachable; see scripts/browser-qa.mjs.
browser-qa:
	@python3 -m http.server $(PORT) --bind 127.0.0.1 --directory web >/dev/null 2>&1 & \
	server=$$!; \
	trap "kill $$server 2>/dev/null" EXIT; \
	FRONTIER_URL=$(URL) node scripts/browser-qa.mjs; \
	status=$$?; \
	kill $$server 2>/dev/null; \
	exit $$status

clean:
	rm -rf build
