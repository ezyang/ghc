TOP=../../../..
include $(TOP)/mk/boilerplate.mk
include $(TOP)/mk/test.mk

.PHONY: bkpcabal01
bkpcabal01:
	@rm -rf package.conf p q h r
	"$(GHC_PKG)" init package.conf
	"$(TEST_HC)" $(TEST_HC_OPTS_NO_RECOMP) -package-db package.conf -outputdir p -this-component-id p --backpack p.bkp
	"$(GHC_PKG)" --enable-multi-instance --no-user-package-db -f package.conf register p.pkg
	"$(TEST_HC)" $(TEST_HC_OPTS_NO_RECOMP) -package-db package.conf -outputdir q -this-component-id q --backpack q.bkp
	"$(GHC_PKG)" --enable-multi-instance --no-user-package-db -f package.conf register q.pkg
	"$(TEST_HC)" $(TEST_HC_OPTS_NO_RECOMP) -package-db package.conf -outputdir h -this-component-id h --backpack h.bkp
	"$(GHC_PKG)" --enable-multi-instance --no-user-package-db -f package.conf register h.pkg
	"$(TEST_HC)" $(TEST_HC_OPTS_NO_RECOMP) -package-db package.conf -outputdir p -this-component-id p --backpack p.bkp -sig-of "H=h:H"
	"$(GHC_PKG)" --enable-multi-instance --no-user-package-db -f package.conf register p-h.pkg
	"$(TEST_HC)" $(TEST_HC_OPTS_NO_RECOMP) -package-db package.conf -outputdir q -this-component-id q --backpack q.bkp -sig-of "H=h:H"
	"$(GHC_PKG)" --enable-multi-instance --no-user-package-db -f package.conf register q-h.pkg
	"$(TEST_HC)" $(TEST_HC_OPTS_NO_RECOMP) -package-db package.conf -outputdir r -this-component-id r --backpack r.bkp
