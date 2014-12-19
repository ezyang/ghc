TOP=../../..
include $(TOP)/mk/boilerplate.mk
include $(TOP)/mk/test.mk

SETUP=../Setup -v0

# This test is for signature being provided by both an external package and
# the local environment providing a signature.

sigcabal03:
	$(MAKE) clean
	'$(GHC_PKG)' field containers id | sed 's/^.*: *//' > containers
	'$(GHC_PKG)' field containers key | sed 's/^.*: *//' > containers_key
	'$(GHC_PKG)' init tmp.d
	'$(TEST_HC)' -v0 --make Setup
	cd p && $(SETUP) clean
	cd p && $(SETUP) configure $(CABAL_MINIMAL_BUILD) --with-ghc='$(TEST_HC)' --ghc-options='$(TEST_HC_OPTS)' --package-db=../tmp.d --prefix='$(PWD)/inst-p' --instantiate-with="Map=Data.Map.Lazy@`cat ../containers`" --ghc-pkg-options="--enable-multi-instance"
	cd p && $(SETUP) build
	cd p && $(SETUP) copy
	cd p && $(SETUP) register --print-ipid > ../p_ipid
	'$(TEST_HC)' $(TEST_HC_OPTS) -package-db=tmp.d -hide-all-packages -package base -package-id "`cat p_ipid`" --make Main.hs -sig-of "Map is `cat containers_key`:Data.Map.Lazy"
	./Main
ifneq "$(CLEANUP)" ""
	$(MAKE) clean
endif

clean :
	'$(GHC_PKG)' unregister --force p >/dev/null 2>&1 || true
	$(RM) -r tmp.d inst-* *.o *.hi */*.o */*.hi */Setup$(exeext) */dist Setup$(exeext)
