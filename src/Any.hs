module Any (
  Any,
  unsafeCoerce,
) where

import qualified GHC.Base
import qualified Unsafe.Coerce as GHC.Base

unsafeCoerce :: a -> b
unsafeCoerce = GHC.Base.unsafeCoerce

type Any = GHC.Base.Any
