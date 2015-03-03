TOP=../..
include $(TOP)/mk/boilerplate.mk
include $(TOP)/mk/test.mk

# -fforce-recomp makes lots of driver tests trivially pass, so we
# filter it out from $(TEST_HC_OPTS).
TEST_HC_OPTS_NO_RECOMP = $(filter-out -fforce-recomp,$(TEST_HC_OPTS))
TEST_HC_OPTS_NO_RECOMP_NO_RTSOPTS = $(filter-out -rtsopts,$(TEST_HC_OPTS_NO_RECOMP))

.PHONY: backpack01

backpack01:
	$(RM) -rf p/out_* out_*
	$(RM) q/*.o q/*.hi foo1 foo2 *.o *.hi
	"$(TEST_HC)" $(TEST_HC_OPTS_NO_RECOMP) --backpack backpack01.bkp
