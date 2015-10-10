TOP=../../..
include $(TOP)/mk/boilerplate.mk
include $(TOP)/mk/test.mk

.PHONY: bkp01c
bkp01c:
	$(RM) -rf bkp01c
	"$(TEST_HC)" $(TEST_HC_OPTS_NO_RECOMP) -dno-debug-output -outputdir bkp01c --backpack bkp01.bkp
