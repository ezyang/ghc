TOP=../../..
include $(TOP)/mk/boilerplate.mk
include $(TOP)/mk/test.mk

# -fforce-recomp makes lots of driver tests trivially pass, so we
# filter it out from $(TEST_HC_OPTS).
TEST_HC_OPTS_NO_RECOMP = $(filter-out -fforce-recomp,$(TEST_HC_OPTS))

clean:
	rm -f *.o *.hi tmp_*

sigof01:
	rm -f *.o *.hi
	'$(TEST_HC)' $(TEST_HC_OPTS_NO_RECOMP) -c A.hs
	'$(TEST_HC)' $(TEST_HC_OPTS_NO_RECOMP) -c B.hsig -sig-of main:A
	'$(TEST_HC)' $(TEST_HC_OPTS_NO_RECOMP) -c Main.hs
	'$(TEST_HC)' $(TEST_HC_OPTS_NO_RECOMP) A.o Main.o -o Main
	./Main

sigof01m:
	rm -rf tmp_sigof01m
	mkdir tmp_sigof01m
	'$(TEST_HC)' $(TEST_HC_OPTS_NO_RECOMP) -outputdir tmp_sigof01m --make Main.hs -sig-of "B is main:A" -o tmp_sigof01m/Main
	tmp_sigof01m/Main
