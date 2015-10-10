module LoadIface where
import Module (Module)
import Avail (AvailInfo)
import TcRnMonad (IfM, TcRnIf)
import HscTypes (ModIface)
import Outputable (SDoc)
import Maybes (MaybeErr)
import ErrUtils (MsgDoc)

loadSysInterface :: SDoc -> Module -> IfM lcl ModIface
computeInterface :: SDoc -> Bool -> Module
                 -> TcRnIf gbl lcl (MaybeErr MsgDoc (ModIface, FilePath))
computeExports :: SDoc -> Bool -> Module
               -> TcRnIf gbl lcl (MaybeErr MsgDoc ([AvailInfo], FilePath))
