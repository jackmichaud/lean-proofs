.PHONY: build validate test catalog journal check check-lean check-web serve browser-qa clean

PORT ?= 4173
URL ?= http://127.0.0.1:$(PORT)/

# Build the library as well as the executable. The executable's root (Leanproofs.Main) does
# not import Leanproofs.Catalog -- it reads the catalog out of the environment at runtime --
# so `lake build frontier` alone succeeds against stale oleans and the audit below would
# then validate a registry that no longer compiles.
build:
	lake build Leanproofs frontier frontier-test

validate: build
	lake exe frontier validate

# Negative fixtures for the audit. `validate` passing on correct entries is no evidence that an
# incorrect one would be rejected, and rejecting is the entire job.
test: build
	lake exe frontier-test

catalog: build
	lake exe frontier export web/data/catalog.json

# Republish the work journal. Every `frontier work` mutation already does this; the target is
# for the case where work/ was edited by hand or merged from a branch.
journal: build
	lake exe frontier work export

# The full gate. Runs in CI; run it before pushing.
check: check-lean check-web

# Kernel audit plus the guarantee that the committed web catalog still matches the registry.
# The comparison is structural rather than byte-for-byte: pretty-printed Lean types move with
# the toolchain, so a mathlib bump should not fail the build over rendering churn.
check-lean: build
	lake exe frontier-test
	lake exe frontier validate
	lake exe frontier export build/frontier.check.json
	python3 scripts/compare-catalog.py build/frontier.check.json web/data/catalog.json
# The journal is mutable untrusted data, so it is *not* compared against a committed copy the
# way the catalog is -- that gate exists because the catalog is derived, trusted data. Reading
# every item is still worth doing: a malformed file must fail the build rather than quietly
# disappear from the board.
	lake exe frontier work list >/dev/null

# Syntax check, then drive the real page in a real browser if one is reachable.
check-web:
	node --check web/app.js
	node --check scripts/browser-qa.mjs
	$(MAKE) browser-qa

serve: catalog
	python3 -m http.server $(PORT) --bind 127.0.0.1 --directory web

# Serves the workspace on a throwaway port and drives it over the Chrome DevTools Protocol.
# Skips with a notice when no CDP endpoint is reachable; see scripts/browser-qa.mjs.
#
# Waiting for the port is not optional. Chrome answers a refused connection with an error page
# that reaches `readyState === 'complete'` and carries an opaque origin, so a run that starts
# before the server has bound does not fail at the navigation -- it limps on and dies several
# steps later inside `localStorage.clear()`, reporting a served-page problem as a script bug.
browser-qa:
	@python3 -m http.server $(PORT) --bind 127.0.0.1 --directory web >/dev/null 2>&1 & \
	server=$$!; \
	trap "kill $$server 2>/dev/null" EXIT; \
	ready=0; \
	for _ in $$(seq 1 50); do \
	  if curl -sf -o /dev/null $(URL); then ready=1; break; fi; \
	  sleep 0.2; \
	done; \
	if [ $$ready -eq 0 ]; then \
	  echo "browser QA FAILED: $(URL) did not start serving within 10s" >&2; \
	  kill $$server 2>/dev/null; \
	  exit 1; \
	fi; \
	FRONTIER_URL=$(URL) node scripts/browser-qa.mjs; \
	status=$$?; \
	kill $$server 2>/dev/null; \
	exit $$status

clean:
	rm -rf build
