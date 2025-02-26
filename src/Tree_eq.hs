module Tree_eq (
  tree_eqMixin,
  tree_eqType,
) where

import Any (unsafeCoerce)
import Encoding (decode, encode)
import Eq (option_eqType, pcanEqMixin, seq_eqType)
import OtDef (Mixin_of, Sort, Type)
import Tree (Tree)

tree_eqMixin :: Type -> Mixin_of (Tree Sort)
tree_eqMixin t0 =
  pcanEqMixin
    (seq_eqType (option_eqType t0))
    (unsafeCoerce encode)
    (unsafeCoerce decode)

tree_eqType :: Type -> Type
tree_eqType t0 =
  unsafeCoerce tree_eqMixin t0
