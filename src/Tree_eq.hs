module Tree_eq (
  tree_eqMixin,
  tree_eqType,
  insert,
  open,
) where

import Any (unsafeCoerce)
import Encoding (decode, encode)
import Eq (option_eqType, pcanEqMixin, seq_eqType)
import OtDef (Mixin_of, Rel, Sort, Type)
import Tree (Tree (Node), bind, by_value, find, g_insert, treeR, without)

tree_eqMixin :: Type -> Mixin_of (Tree Sort)
tree_eqMixin t0 =
  pcanEqMixin
    (seq_eqType (option_eqType t0))
    (unsafeCoerce encode)
    (unsafeCoerce decode)

tree_eqType :: Type -> Type
tree_eqType t0 =
  unsafeCoerce tree_eqMixin t0

insert :: Type -> (Rel Sort) -> Sort -> (([]) Sort) -> ([]) Sort
insert t0 r0 =
  g_insert (tree_eqType t0) (unsafeCoerce treeR t0 r0)

open ::
  Type ->
  (Rel Sort) ->
  ((Tree Sort) -> Prelude.Maybe (Tree Sort)) ->
  Sort ->
  (Tree Sort) ->
  Prelude.Maybe (Tree Sort)
open t0 r0 f vo t1 =
  case t1 of
    Node v cs ->
      case bind f (find (by_value t0 vo) cs) of
        Prelude.Just fch ->
          Prelude.Just
            ( Node
                v
                (unsafeCoerce insert t0 r0 fch (without t0 vo cs))
            )
        Prelude.Nothing -> Prelude.Nothing
