TOP=../..
include $(TOP)/mk/boilerplate.mk
include $(TOP)/mk/test.mk

.PHONY: plugins01

plugins01:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make -v0 plugins01.hs -package-db simple-plugin/pkg.plugins01/local.package.conf -fplugin Simple.Plugin -fplugin-opt Simple.Plugin:Irrelevant_Option -package simple-plugin
	./plugins01

.PHONY: frontend01
frontend01:
	$(RM) FrontendPlugin.hi FrontendPlugin.o frontend01 frontend01.hi frontend.o
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) -Wall -package ghc -c FrontendPlugin.hs
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --frontend FrontendPlugin -ffrontend-opt foobar frontend01
	./frontend01
