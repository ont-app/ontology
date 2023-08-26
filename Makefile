
## Validate deps.edn

.PHONEY: validate-deps
validate-deps:
	clojure -T:build validate-deps

## Update dependencies as needed....
outdated:
	clojure -M:outdated

## Testing ....
.PHONY: test-jvm validate-deps
test-jvm:
	clojure -T:build test

.PHONY: clean-all
clean-all:
	clojure -T:build clean :include-caches? true

test-all: clean-all test-jvm # test-js test-node

## Style ....
kondo:
	clojure -M:kondo --lint src

## Security ...
### assumes that nvd-clojure/nvd-clojure tool has been installed
### see also https://github.com/rm-hull/nvd-clojure
nvd:
	clojure -J-Dclojure.main.report=stderr -Tnvd nvd.task/check :classpath \"$(shell clojure -Spath)\"


## Generate documentation ...
codox:
	clojure -X:codox

## Publishing...
uberjar: validate-deps
	clojure -T:build ci

install: uberjar
	clojure -T:build install

deploy: uberjar
	clojure -T:build deploy
