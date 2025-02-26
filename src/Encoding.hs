module Encoding (
  encode,
  decode,
) where

import Tree (Tree (Node), behead, flatten, foldr, fst, head, map, ohead, rcons, snd)

encode :: (Tree a1) -> ([]) (Prelude.Maybe a1)
encode t0 =
  case t0 of
    Node x f ->
      (:)
        (Prelude.Just x)
        (rcons (flatten (Tree.map encode f)) Prelude.Nothing)

decode_step ::
  (Prelude.Maybe a1) ->
  ( (,)
      (([]) (Tree a1))
      (([]) (([]) (Tree a1)))
  ) ->
  (,)
    (([]) (Tree a1))
    (([]) (([]) (Tree a1)))
decode_step c fs =
  case c of
    Prelude.Just x ->
      (,)
        ((:) (Node x (Tree.fst fs)) (Tree.head ([]) (Tree.snd fs)))
        (behead (Tree.snd fs))
    Prelude.Nothing -> (,) ([]) ((:) (Tree.fst fs) (Tree.snd fs))

decode :: (([]) (Prelude.Maybe a1)) -> Prelude.Maybe (Tree a1)
decode c =
  ohead (Tree.fst (Tree.foldr decode_step ((,) ([]) ([])) c))
