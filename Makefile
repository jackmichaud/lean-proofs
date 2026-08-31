.PHONY: build validate catalog check serve browser-qa

build:
	lake build frontier

validate: build
	lake exe frontier validate

catalog: build
	lake exe frontier export web/data/catalog.json

check: build
	lake exe frontier validate
	node --check web/app.js
	node --check scripts/browser-qa.mjs
	lake exe frontier export build/frontier.check.json
	cmp build/frontier.check.json web/data/catalog.json

serve: catalog
	python3 -m http.server 4173 --bind 127.0.0.1 --directory web

browser-qa:
	node scripts/browser-qa.mjs
