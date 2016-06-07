import Data.Typeable
import Data.Proxy
import Prelude

x = typeRep (Proxy::Proxy '(Int,Int))
