TOP=../../..
include $(TOP)/mk/boilerplate.mk
include $(TOP)/mk/test.mk

# -fforce-recomp makes lots of driver tests trivially pass, so we
# filter it out from $(TEST_HC_OPTS).
TEST_HC_OPTS_NO_RECOMP = $(filter-out -fforce-recomp,$(TEST_HC_OPTS))

S05_OPTS=$(TEST_HC_OPTS_NO_RECOMP) -outputdir tmp_sigof05 -i -itmp_sigof05
sigof05:
	rm -rf tmp_sigof05
	mkdir tmp_sigof05
	'$(GHC_PKG)' field containers key | sed 's/^.*: *//' > tmp_sigof05/containers
	'$(TEST_HC)' $(S05_OPTS) -c Data/Map.hsig -sig-of "Data.Map is `cat tmp_sigof05/containers`:Data.Map"
	'$(TEST_HC)' $(S05_OPTS) Main.hs -sig-of "Data.Map is `cat tmp_sigof05/containers`:Data.Map" -o tmp_sigof05/Main
	tmp_sigof05/Main

S05F_OPTS=$(TEST_HC_OPTS_NO_RECOMP) -outputdir tmp_sigof05f -i -itmp_sigof05f
sigof05f:
	rm -rf tmp_sigof05f
	mkdir tmp_sigof05f
	'$(GHC_PKG)' field containers key | sed 's/^.*: *//' > tmp_sigof05f/containers
	'$(TEST_HC)' $(S05_OPTS) -c Data/Map.hsig -sig-of "Data.Map is `cat tmp_sigof05f/containers`:Data.Map.Strict"
	! '$(TEST_HC)' $(S05_OPTS) -c Main.hs -sig-of "Data.Map is `cat tmp_sigof05f/containers`:Data.Map.Strict"

S05M_OPTS=$(TEST_HC_OPTS_NO_RECOMP) -outputdir tmp_sigof05m
sigof05m:
	rm -rf tmp_sigof05m
	mkdir tmp_sigof05m
	'$(GHC_PKG)' field containers key | sed 's/^.*: *//' > tmp_sigof05m/containers
	'$(TEST_HC)' $(S05M_OPTS) --make Main.hs -sig-of "Data.Map is `cat tmp_sigof05m/containers`:Data.Map" -o tmp_sigof05m/Main
	tmp_sigof05m/Main

S05FM_OPTS=$(TEST_HC_OPTS_NO_RECOMP) -outputdir tmp_sigof05fm
sigof05fm:
	rm -rf tmp_sigof05fm
	mkdir tmp_sigof05fm
	'$(GHC_PKG)' field containers key | sed 's/^.*: *//' > tmp_sigof05fm/containers
	! '$(TEST_HC)' $(S05FM_OPTS) --make Main.hs -sig-of "Data.Map is `cat tmp_sigof05fm/containers`:Data.Map.Strict" -o tmp_sigof05fm/Main
