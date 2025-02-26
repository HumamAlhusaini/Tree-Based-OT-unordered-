module Pred (
  Pred,
  predType,
  Pred_sort,
  PredType0 (PredType),
  Mem_pred (Mem),
) where

import Any (Any, unsafeCoerce)

type Pred t = t -> Prelude.Bool

type Pred_sort t = Any

data PredType0 t
  = PredType (Any -> Pred t) (Any -> Mem_pred t)

predType :: (a2 -> Pred a1) -> PredType0 a1
predType =
  mkPredType

newtype Mem_pred t
  = Mem (Pred t)

mkPredType :: (a2 -> a1 -> Prelude.Bool) -> PredType0 a1
mkPredType toP =
  PredType (unsafeCoerce toP) (Mem . unsafeCoerce toP)
