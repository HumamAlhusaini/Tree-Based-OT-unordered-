module OtDef (
  OTBase (Build_OTBase),
  OTComp (Build_OTComp),
  Sort,
  Reflect (ReflectF, ReflectT),
  Mixin_of (Mixin),
  Type,
  Rel,
  Axiom,
  Pred,
) where

import Any (Any)
import Pred (Pred)

type Sort = Any

type Type = Mixin_of Any

type Rel t = t -> Pred t

type Axiom t = t -> t -> Reflect

data Mixin_of t
  = Mixin (Rel t) (Axiom t)

data Reflect
  = ReflectT
  | ReflectF

data OTBase x cmd
  = Build_OTBase
      (cmd -> x -> Prelude.Maybe x)
      ( cmd ->
        cmd ->
        Prelude.Bool ->
        [] cmd
      )

data OTComp x cmd
  = Build_OTComp (cmd -> Prelude.Integer) (cmd -> Prelude.Integer)
