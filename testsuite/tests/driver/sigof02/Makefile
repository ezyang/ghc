TOP=../../..
include $(TOP)/mk/boilerplate.mk
include $(TOP)/mk/test.mk

# -fforce-recomp makes lots of driver tests trivially pass, so we
# filter it out from $(TEST_HC_OPTS).
TEST_HC_OPTS_NO_RECOMP = $(filter-out -fforce-recomp,$(TEST_HC_OPTS))

clean:
	rm -rf tmp_* containers

containers:
	'$(GHC_PKG)' field containers key | sed 's/^.*: *//' > containers

S02_OPTS=$(TEST_HC_OPTS_NO_RECOMP) -outputdir tmp_sigof02 -i -itmp_sigof02
sigof02: containers
	rm -rf tmp_sigof02
	mkdir tmp_sigof02
	'$(TEST_HC)' $(S02_OPTS) -c Map.hsig -sig-of "`cat containers`:Data.Map.Strict"
	'$(TEST_HC)' $(S02_OPTS) -c Main.hs
	'$(TEST_HC)' $(S02_OPTS) -package containers tmp_sigof02/Main.o -o tmp_sigof02/StrictMain
	! ./tmp_sigof02/StrictMain
	'$(TEST_HC)' $(S02_OPTS) -c Map.hsig -sig-of "`cat containers`:Data.Map.Lazy"
	'$(TEST_HC)' $(S02_OPTS) -c Main.hs
	'$(TEST_HC)' $(S02_OPTS) -package containers tmp_sigof02/Main.o -o tmp_sigof02/LazyMain
	./tmp_sigof02/LazyMain

S02T_OPTS=$(TEST_HC_OPTS_NO_RECOMP) -fno-code -fwrite-interface -outputdir tmp_sigof02t -i -itmp_sigof02t
sigof02t:
	rm -rf tmp_sigof02t
	mkdir tmp_sigof02t
	'$(TEST_HC)' $(S02T_OPTS) -c Map.hsig
	'$(TEST_HC)' $(S02T_OPTS) -c Main.hs

S02M_OPTS=$(TEST_HC_OPTS_NO_RECOMP) -outputdir tmp_sigof02m
sigof02m: containers
	rm -rf tmp_sigof02m
	mkdir tmp_sigof02m
	'$(TEST_HC)' $(S02M_OPTS) --make Main.hs -sig-of "Map is `cat containers`:Data.Map.Strict" -o tmp_sigof02m/StrictMain
	! ./tmp_sigof02m/StrictMain
	'$(TEST_HC)' $(S02M_OPTS) --make Main.hs -sig-of "Map is `cat containers`:Data.Map.Lazy" -o tmp_sigof02m/LazyMain
	./tmp_sigof02m/LazyMain

sigof02mt:
	rm -rf tmp_sigof02mt
	mkdir tmp_sigof02mt
	'$(TEST_HC)' $(TEST_HC_OPTS_NO_RECOMP) -outputdir tmp_sigof02mt --make Main.hs -fno-code -fwrite-interface

S02D_OPTS=$(TEST_HC_OPTS_NO_RECOMP) -outputdir tmp_sigof02d -i -itmp_sigof02d
sigof02d: containers
	rm -rf tmp_sigof02d
	mkdir tmp_sigof02d
	'$(TEST_HC)' $(S02D_OPTS) -c Map.hsig -sig-of "`cat containers`:Data.Map.Lazy"
	'$(TEST_HC)' $(S02D_OPTS) -c MapAsSet.hsig -sig-of "`cat containers`:Data.Map.Lazy"
	'$(TEST_HC)' $(S02D_OPTS) -c Double.hs
	'$(TEST_HC)' $(S02D_OPTS) -package containers tmp_sigof02d/Main.o -o tmp_sigof02d/Double
	./tmp_sigof02d/Double

S02DT_OPTS=$(TEST_HC_OPTS_NO_RECOMP) -outputdir tmp_sigof02dt -i -itmp_sigof02dt -fno-code -fwrite-interface
sigof02dt:
	rm -rf tmp_sigof02dt
	mkdir tmp_sigof02dt
	'$(TEST_HC)' $(S02DT_OPTS) -c Map.hsig
	'$(TEST_HC)' $(S02DT_OPTS) -c MapAsSet.hsig
	! '$(TEST_HC)' $(S02DT_OPTS) -c Double.hs

sigof02dm: containers
	rm -rf tmp_sigof02dm
	mkdir tmp_sigof02dm
	'$(TEST_HC)' $(TEST_HC_OPTS_NO_RECOMP) -outputdir tmp_sigof02dm --make Double.hs -sig-of "Map is `cat containers`:Data.Map.Lazy, MapAsSet is `cat containers`:Data.Map.Lazy" -o tmp_sigof02dm/Double
	./tmp_sigof02dm/Double

sigof02dmt:
	rm -rf tmp_sigof02dmt
	mkdir tmp_sigof02dmt
	# doesn't typecheck due to lack of alias
	! '$(TEST_HC)' $(TEST_HC_OPTS_NO_RECOMP) -outputdir tmp_sigof02dmt -fno-code -fwrite-interface --make Double.hs -o tmp_sigof02dm/Double
