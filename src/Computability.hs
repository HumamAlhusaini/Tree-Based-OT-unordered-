module Computability (

) where

import Encoding (encode)
import Fs (Raw_fs_cmd (RawCreate, RawOpen))
import Tree (Tree, addn, foldr, map)

weight :: (Tree a1) -> Prelude.Integer
weight t0 =
  Tree.foldr
    addn
    0
    ( Tree.map
        ( \o -> case o of
            Prelude.Just _ -> succ 0
            Prelude.Nothing -> 0
        )
        (encode t0)
    )

raw_fs_sz0 :: Raw_fs_cmd -> Prelude.Integer
raw_fs_sz0 x =
  case x of
    RawCreate t0 -> weight t0
    RawOpen _ c -> raw_fs_sz0 c
    _ -> succ 0

raw_fs_si0 :: Raw_fs_cmd -> Prelude.Integer
raw_fs_si0 x =
  case x of
    RawCreate t0 -> weight t0
    RawOpen _ c -> raw_fs_si0 c
    _ -> 0

raw_fs_sz :: (([]) Raw_fs_cmd) -> Prelude.Integer
raw_fs_sz x =
  foldl addn 0 (Tree.map raw_fs_sz0 x)

raw_fs_si :: (([]) Raw_fs_cmd) -> Prelude.Integer
raw_fs_si x =
  foldl addn 0 (Tree.map raw_fs_si0 x)
