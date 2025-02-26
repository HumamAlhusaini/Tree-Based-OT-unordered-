{-# OPTIONS_GHC -cpp -XMagicHash #-}

{- For Hugs, use the option -F"cpp -P -traditional" -}

module Fs where

import Eq (eq_op, eq_rec_r, seq_predType)
import OtDef (Axiom, Mixin_of (Mixin), Reflect (ReflectF, ReflectT), Rel, Sort, Type)
import Tree (Tree (Node), all, bind, children, filter, flatten, funcomp, has, in_mem, locked, map, mem, sorted, true_some, value)
import Tree_eq (tree_eqType)

import qualified Prelude

#ifdef __GLASGOW_HASKELL__
import qualified Unsafe.Coerce as GHC.Base
#else
-- HUGS
import qualified IOExts
#endif

unsafeCoerce :: a -> b
unsafeCoerce = GHC.Base.unsafeCoerce#

__ :: any
__ = Prelude.error "Logical or arity value used"

find :: (a1 -> Prelude.Bool) -> (([]) a1) -> Prelude.Maybe a1
find p xs =
  case xs of
    ([]) -> Prelude.Nothing
    (:) xh xt ->
      case p xh of
        Prelude.True -> Prelude.Just xh
        Prelude.False -> find p xt

seqminus :: Type -> (([]) Sort) -> (([]) Sort) -> ([]) Sort
seqminus x x0 y =
  filter
    ( \z ->
        Prelude.not (in_mem z (mem (seq_predType x) (unsafeCoerce y)))
    )
    x0

g_insert :: Type -> (Rel Sort) -> Sort -> (([]) Sort) -> ([]) Sort
g_insert x r0 x0 xs =
  case xs of
    ([]) -> (:) x0 ([])
    (:) xh xt ->
      case eq_op x x0 xh of
        Prelude.True -> xs
        Prelude.False ->
          case r0 x0 xh of
            Prelude.True -> (:) x0 xs
            Prelude.False -> (:) xh (g_insert x r0 x0 xt)

is_tree_sorted :: Type -> (Rel Sort) -> (Tree Sort) -> Prelude.Bool
is_tree_sorted t0 r0 t1 =
  case t1 of
    Node _ cs ->
      (Prelude.&&) (sorted r0 (map value cs)) (all (is_tree_sorted t0 r0) cs)

type Sorted_tree =
  Tree Sort

-- singleton inductive, whose constructor was STree

treeOf :: Type -> (Rel Sort) -> Sorted_tree -> Tree Sort
treeOf _ _ s =
  s

sNode :: Type -> (Rel Sort) -> Sort -> Sorted_tree
sNode _ _ t0 =
  Node t0 ([])

treeR :: Type -> (Rel Sort) -> (Tree Sort) -> (Tree Sort) -> Prelude.Bool
treeR _ r0 x y =
  r0 (value x) (value y)

by_value :: Type -> Sort -> (Tree Sort) -> Prelude.Bool
by_value t0 v =
  funcomp () (eq_op t0 v) value

insert :: Type -> (Rel Sort) -> Sort -> (([]) Sort) -> ([]) Sort
insert t0 r0 =
  g_insert (tree_eqType t0) (unsafeCoerce treeR t0 r0)

without :: Type -> Sort -> (([]) (Tree Sort)) -> ([]) (Tree Sort)
without t0 v =
  filter (funcomp () Prelude.not (by_value t0 v))

without' :: Type -> Sort -> (([]) (Tree Sort)) -> ([]) (Tree Sort)
without' t0 =
  locked (without t0)

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

t :: Type
t =
  Prelude.error "AXIOM TO BE REALIZED"

r :: Rel Sort
r =
  Prelude.error "AXIOM TO BE REALIZED"

data Raw_fs_cmd
  = RawEdit Sort Sort
  | RawCreate (Tree Sort)
  | RawRemove (Tree Sort)
  | RawOpen Sort Raw_fs_cmd

raw_fs_cmd_rect ::
  (Sort -> Sort -> a1) ->
  ((Tree Sort) -> a1) ->
  ( ( Tree
        Sort
    ) ->
    a1
  ) ->
  (Sort -> Raw_fs_cmd -> a1 -> a1) ->
  Raw_fs_cmd ->
  a1
raw_fs_cmd_rect f f0 f1 f2 r0 =
  case r0 of
    RawEdit s s0 -> f s s0
    RawCreate t0 -> f0 t0
    RawRemove t0 -> f1 t0
    RawOpen s r1 -> f2 s r1 (raw_fs_cmd_rect f f0 f1 f2 r1)

raw_fs_inv :: Raw_fs_cmd -> Raw_fs_cmd
raw_fs_inv cmd =
  case cmd of
    RawEdit l k -> RawEdit k l
    RawCreate t0 -> RawRemove t0
    RawRemove t0 -> RawCreate t0
    RawOpen l c -> RawOpen l (raw_fs_inv c)

eq_cmd :: Raw_fs_cmd -> Raw_fs_cmd -> Prelude.Bool
eq_cmd t1 t2 =
  case t1 of
    RawEdit l k ->
      case t2 of
        RawEdit l2 k2 -> (Prelude.&&) (eq_op t l l2) (eq_op t k k2)
        _ -> Prelude.False
    RawCreate t0 ->
      case t2 of
        RawCreate t3 ->
          eq_op (tree_eqType t) (unsafeCoerce t0) (unsafeCoerce t3)
        _ -> Prelude.False
    RawRemove t0 ->
      case t2 of
        RawRemove t3 ->
          eq_op (tree_eqType t) (unsafeCoerce t0) (unsafeCoerce t3)
        _ -> Prelude.False
    RawOpen l c ->
      case t2 of
        RawOpen l2 c2 -> (Prelude.&&) (eq_op t l l2) (eq_cmd c c2)
        _ -> Prelude.False

eq_cmdK :: Axiom Raw_fs_cmd
eq_cmdK _top_assumption_ =
  let _evar_0_ = \l k __top_assumption_ ->
        let _evar_0_ = \l2 k2 ->
              let _evar_0_ = \_ ->
                    let _evar_0_ = \_ _ -> ReflectT
                     in let _evar_0_0 = \_ _ -> ReflectF
                         in case eq_op t k k2 of
                              Prelude.True -> _evar_0_ __ __
                              Prelude.False -> _evar_0_0 __ __
               in let _evar_0_0 = \_ -> ReflectF
                   in case eq_op t l l2 of
                        Prelude.True -> _evar_0_ __
                        Prelude.False -> _evar_0_0 __
         in let _evar_0_0 = \_ -> ReflectF
             in let _evar_0_1 = \_ -> ReflectF
                 in let _evar_0_2 = \_ _ -> ReflectF
                     in case __top_assumption_ of
                          RawEdit x x0 -> _evar_0_ x x0
                          RawCreate x -> _evar_0_0 x
                          RawRemove x -> _evar_0_1 x
                          RawOpen x x0 -> _evar_0_2 x x0
   in let _evar_0_0 = \t0 __top_assumption_ ->
            let _evar_0_0 = \_ _ -> ReflectF
             in let _evar_0_1 = \t2 ->
                      let _evar_0_1 = \_ -> ReflectT
                       in let _evar_0_2 = \_ -> ReflectF
                           in case eq_op (tree_eqType t) t0 t2 of
                                Prelude.True -> _evar_0_1 __
                                Prelude.False -> _evar_0_2 __
                 in let _evar_0_2 = \_ -> ReflectF
                     in let _evar_0_3 = \_ _ -> ReflectF
                         in case __top_assumption_ of
                              RawEdit x x0 -> _evar_0_0 x x0
                              RawCreate x -> unsafeCoerce _evar_0_1 x
                              RawRemove x -> _evar_0_2 x
                              RawOpen x x0 -> _evar_0_3 x x0
       in let _evar_0_1 = \t0 __top_assumption_ ->
                let _evar_0_1 = \_ _ -> ReflectF
                 in let _evar_0_2 = \_ -> ReflectF
                     in let _evar_0_3 = \t2 ->
                              let _evar_0_3 = \_ -> ReflectT
                               in let _evar_0_4 = \_ -> ReflectF
                                   in case eq_op (tree_eqType t) t0 t2 of
                                        Prelude.True -> _evar_0_3 __
                                        Prelude.False -> _evar_0_4 __
                         in let _evar_0_4 = \_ _ -> ReflectF
                             in case __top_assumption_ of
                                  RawEdit x x0 -> _evar_0_1 x x0
                                  RawCreate x -> _evar_0_2 x
                                  RawRemove x -> unsafeCoerce _evar_0_3 x
                                  RawOpen x x0 -> _evar_0_4 x x0
           in let _evar_0_2 = \l c _ __top_assumption_ ->
                    let _evar_0_2 = \_ _ -> ReflectF
                     in let _evar_0_3 = \_ -> ReflectF
                         in let _evar_0_4 = \_ -> ReflectF
                             in let _evar_0_5 = \l2 c2 ->
                                      let _evar_0_5 = \_ ->
                                            eq_rec_r
                                              l2
                                              ( let _evar_0_5 = \_ -> ReflectT
                                                 in let _evar_0_6 = \_ -> ReflectF
                                                     in case eq_cmd c c2 of
                                                          Prelude.True -> _evar_0_5 __
                                                          Prelude.False -> _evar_0_6 __
                                              )
                                              l
                                       in let _evar_0_6 = \_ -> ReflectF
                                           in case eq_op t l l2 of
                                                Prelude.True -> _evar_0_5 __
                                                Prelude.False -> _evar_0_6 __
                                 in case __top_assumption_ of
                                      RawEdit x x0 -> _evar_0_2 x x0
                                      RawCreate x -> _evar_0_3 x
                                      RawRemove x -> _evar_0_4 x
                                      RawOpen x x0 -> _evar_0_5 x x0
               in raw_fs_cmd_rect
                    _evar_0_
                    (unsafeCoerce _evar_0_0)
                    (unsafeCoerce _evar_0_1)
                    _evar_0_2
                    _top_assumption_

cmd_eqMixin :: Mixin_of Raw_fs_cmd
cmd_eqMixin =
  Mixin eq_cmd eq_cmdK

cmd_eqType :: Type
cmd_eqType =
  unsafeCoerce cmd_eqMixin

data Fs_cmd
  = Edit Sort Sort
  | Create Sorted_tree
  | Remove Sorted_tree
  | Open Sort Fs_cmd

fs_to_raw_fs :: Fs_cmd -> Raw_fs_cmd
fs_to_raw_fs c =
  case c of
    Edit l k -> RawEdit l k
    Create c0 -> RawCreate (treeOf t r c0)
    Remove t0 -> RawRemove (treeOf t r t0)
    Open l c0 -> RawOpen l (fs_to_raw_fs c0)

fs_inv :: Fs_cmd -> Fs_cmd
fs_inv cmd =
  case cmd of
    Edit l k -> Edit k l
    Create t0 -> Remove t0
    Remove t0 -> Create t0
    Open l c -> Open l (fs_inv c)

raw_fs_interp :: Raw_fs_cmd -> (Tree Sort) -> Prelude.Maybe (Tree Sort)
raw_fs_interp c t0 =
  case t0 of
    Node v cs ->
      case c of
        RawEdit ve ve' ->
          bind
            ( \te ->
                let cs' = without' t ve cs
                 in case te of
                      Node _ cste ->
                        true_some
                          (Prelude.not (has (by_value t ve') cs'))
                          ( Node
                              v
                              (unsafeCoerce insert t r (Node ve' cste) cs')
                          )
            )
            (find (by_value t ve) cs)
        RawCreate tc ->
          true_some
            (Prelude.not (has (by_value t (value tc)) cs))
            ( Node
                v
                (unsafeCoerce insert t r tc cs)
            )
        RawRemove tr ->
          bind
            ( \tr' ->
                true_some
                  (eq_op (tree_eqType t) (unsafeCoerce tr) (unsafeCoerce tr'))
                  ( Node
                      v
                      (without' t (value tr) cs)
                  )
            )
            (find (by_value t (value tr)) cs)
        RawOpen vo co -> open t r (\t1 -> raw_fs_interp co t1) vo t0

data Ins_cmd
  = Ins Sort
  | IOpen Sort Ins_cmd

ins_fs :: Ins_cmd -> Raw_fs_cmd
ins_fs cmd =
  case cmd of
    Ins t0 -> RawCreate (Node t0 ([]))
    IOpen t0 c -> RawOpen t0 (ins_fs c)

ins_fs' :: Ins_cmd -> Fs_cmd
ins_fs' cmd =
  case cmd of
    Ins t0 -> Create (sNode t r t0)
    IOpen t0 c -> Open t0 (ins_fs' c)

eq_ins :: Ins_cmd -> Ins_cmd -> Prelude.Bool
eq_ins t1 t2 =
  case t1 of
    Ins t3 ->
      case t2 of
        Ins t4 -> eq_op t t3 t4
        IOpen _ _ -> Prelude.False
    IOpen l c ->
      case t2 of
        Ins _ -> Prelude.False
        IOpen l2 c2 -> (Prelude.&&) (eq_op t l l2) (eq_ins c c2)

subdiv :: (Tree Sort) -> ([]) Raw_fs_cmd
subdiv t0 =
  case t0 of
    Node v cs ->
      (:)
        (RawCreate (Node v ([])))
        (map (\y -> RawOpen v y) (flatten (map subdiv cs)))

subdiv' :: (Tree Sort) -> ([]) Ins_cmd
subdiv' t0 =
  case t0 of
    Node v cs ->
      (:)
        (Ins v)
        (map (\y -> IOpen v y) (flatten (map subdiv' cs)))

ins_it :: Ins_cmd -> Ins_cmd -> Prelude.Bool -> ([]) Ins_cmd
ins_it x y f =
  case x of
    Ins t1 ->
      case y of
        Ins t2 ->
          case eq_op t t1 t2 of
            Prelude.True -> ([])
            Prelude.False -> (:) (Ins t1) ([])
        IOpen _ _ -> (:) x ([])
    IOpen t1 c1 ->
      case y of
        Ins _ -> (:) x ([])
        IOpen t2 c2 ->
          case eq_op t t1 t2 of
            Prelude.True -> map (\x0 -> IOpen t1 x0) (ins_it c1 c2 f)
            Prelude.False -> (:) x ([])

merge_trees :: (Tree Sort) -> (Tree Sort) -> ([]) Raw_fs_cmd
merge_trees x y =
  unsafeCoerce seqminus cmd_eqType (subdiv x) (subdiv y)

raw_fs_it :: Raw_fs_cmd -> Raw_fs_cmd -> Prelude.Bool -> ([]) Raw_fs_cmd
raw_fs_it x y f =
  let instead = \a b -> (:) (raw_fs_inv a) ((:) b ([]))
   in case x of
        RawEdit xl xk ->
          case y of
            RawEdit yl yk ->
              case eq_op t xl yl of
                Prelude.True ->
                  case eq_op t xk yk of
                    Prelude.True -> ([])
                    Prelude.False ->
                      case f of
                        Prelude.True -> ([])
                        Prelude.False -> (:) (RawEdit yk xk) ([])
                Prelude.False ->
                  case eq_op t xk yk of
                    Prelude.True -> (:) (RawEdit yk yl) ([])
                    Prelude.False -> (:) x ([])
            RawCreate yt ->
              case eq_op t xk (value yt) of
                Prelude.True -> instead y x
                Prelude.False -> (:) x ([])
            RawRemove yt ->
              case eq_op t xl (value yt) of
                Prelude.True -> ([])
                Prelude.False -> (:) x ([])
            RawOpen _ _ -> (:) x ([])
        RawCreate xt ->
          case y of
            RawEdit _ yk ->
              case eq_op t (value xt) yk of
                Prelude.True -> ([])
                Prelude.False -> (:) x ([])
            RawCreate yt ->
              case eq_op t (value xt) (value yt) of
                Prelude.True -> merge_trees xt yt
                Prelude.False -> (:) x ([])
            _ -> (:) x ([])
        RawRemove xt ->
          case y of
            RawEdit yl yk ->
              case eq_op t yl (value xt) of
                Prelude.True -> (:) (RawRemove (Node yk (children xt))) ([])
                Prelude.False -> (:) x ([])
            RawCreate _ -> (:) x ([])
            RawRemove yt ->
              case eq_op t (value xt) (value yt) of
                Prelude.True -> ([])
                Prelude.False -> (:) x ([])
            RawOpen yl yc ->
              case eq_op t (value xt) yl of
                Prelude.True ->
                  case raw_fs_interp yc xt of
                    Prelude.Just t0 -> (:) (RawRemove t0) ([])
                    Prelude.Nothing -> ([])
                Prelude.False -> (:) x ([])
        RawOpen xl xc ->
          case y of
            RawEdit yl yk ->
              case eq_op t xl yl of
                Prelude.True -> (:) (RawOpen yk xc) ([])
                Prelude.False -> (:) x ([])
            RawCreate _ -> (:) x ([])
            RawRemove yt ->
              case eq_op t (value yt) xl of
                Prelude.True -> ([])
                Prelude.False -> (:) x ([])
            RawOpen yl yc ->
              case eq_op t xl yl of
                Prelude.True -> map (\x0 -> RawOpen xl x0) (raw_fs_it xc yc f)
                Prelude.False -> (:) x ([])

ins_interp :: Ins_cmd -> Sorted_tree -> Prelude.Maybe (Tree Sort)
ins_interp c t0 =
  raw_fs_interp (fs_to_raw_fs (ins_fs' c)) (treeOf t r t0)

sorted_option :: (Prelude.Maybe (Tree Sort)) -> Prelude.Bool
sorted_option x =
  case x of
    Prelude.Just t0 -> is_tree_sorted t r t0
    Prelude.Nothing -> Prelude.True

so_st :: (Prelude.Maybe (Tree Sort)) -> Prelude.Maybe Sorted_tree
so_st t0 =
  let _evar_0_ = \t1 -> Prelude.Just t1
   in let _evar_0_0 = \_ -> Prelude.Nothing
       in case t0 of
            Prelude.Just x -> _evar_0_ x
            Prelude.Nothing -> _evar_0_0 __

ins_sorted :: Ins_cmd -> Sorted_tree -> Prelude.Maybe Sorted_tree
ins_sorted c t0 =
  so_st (raw_fs_interp (fs_to_raw_fs (ins_fs' c)) t0)

firstP :: Ins_cmd -> Sort
firstP x =
  case x of
    Ins t0 -> t0
    IOpen t0 _ -> t0
