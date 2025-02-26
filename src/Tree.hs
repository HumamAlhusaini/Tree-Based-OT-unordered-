module Tree (
  Tree (Node),
  idP,
  sub,
  cat,
  interp,
  flatten,
  rcons,
  Tree.map,
  Tree.fst,
  Tree.head,
  Tree.snd,
  Tree.all,
  Tree.foldr,
  behead,
  ohead,
  filter,
  addn,
  in_mem,
  bind,
  mem,
  sorted,
  value,
  locked,
  funcomp,
  children,
  true_some,
  has,
  g_insert,
  treeR,
  without,
  find,
  by_value,
  treeOf,
  without',
  Sorted_tree,
  sNode,
  seqminus,
  is_tree_sorted,
) where

import Any (unsafeCoerce)
import Eq (eq_op, seq_predType)
import OtDef (OTBase (Build_OTBase), Pred, Reflect (ReflectF, ReflectT), Rel, Sort, Type)
import Pred (Mem_pred (Mem), PredType0 (PredType), Pred_sort)

fst :: (,) a1 a2 -> a1
fst p =
  case p of
    (,) x _ -> x

snd :: (,) a1 a2 -> a2
snd p =
  case p of
    (,) _ y -> y

sub :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
sub n m = Prelude.max 0 (n Prelude.- m)

idP :: Prelude.Bool -> Reflect
idP b1 =
  case b1 of
    Prelude.True -> ReflectT
    Prelude.False -> ReflectF

rcons :: [] a1 -> a1 -> [] a1
rcons s z =
  case s of
    [] -> [z]
    (:) x s' -> (:) x (rcons s' z)

foldr :: (a1 -> a2 -> a2) -> a2 -> [] a1 -> a2
foldr f z0 s =
  case s of
    [] -> z0
    (:) x s' -> f x (Tree.foldr f z0 s')

flatten :: [] ([] a1) -> [] a1
flatten =
  Tree.foldr cat []

cat :: [] a1 -> [] a1 -> [] a1
cat s1 s2 =
  case s1 of
    [] -> s2
    (:) x s1' -> (:) x (cat s1' s2)

ohead :: [] a1 -> Prelude.Maybe a1
ohead s =
  case s of
    [] -> Prelude.Nothing
    (:) x _ -> Prelude.Just x

head :: a1 -> [] a1 -> a1
head x0 s =
  case s of
    [] -> x0
    (:) x _ -> x

behead :: [] a1 -> [] a1
behead s =
  case s of
    [] -> []
    (:) _ s' -> s'

interp :: OTBase a1 a2 -> a2 -> a1 -> Prelude.Maybe a1
interp oTBase =
  case oTBase of
    Build_OTBase interp0 _ -> interp0

pred_of_mem :: Mem_pred a1 -> Pred_sort a1
pred_of_mem mp =
  case mp of
    Mem p -> unsafeCoerce p

mem :: PredType0 a1 -> Pred_sort a1 -> Mem_pred a1
mem pT =
  case pT of
    PredType _ s -> s

in_mem :: a1 -> Mem_pred a1 -> Prelude.Bool
in_mem x mp =
  unsafeCoerce pred_of_mem mp x

addn_rec :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
addn_rec =
  (Prelude.+)

addn :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
addn =
  addn_rec

-- singleton inductive, whose constructor was exist

locked :: a1 -> a1
locked x =
  x

funcomp :: () -> (a2 -> a1) -> (a3 -> a2) -> a3 -> a1
funcomp _ f g x =
  f (g x)

has :: Pred a1 -> [] a1 -> Prelude.Bool
has a s =
  case s of
    [] -> Prelude.False
    (:) x s' -> (Prelude.||) (a x) (has a s')

all :: Pred a1 -> [] a1 -> Prelude.Bool
all a s =
  case s of
    [] -> Prelude.True
    (:) x s' -> (Prelude.&&) (a x) (Tree.all a s')

map :: (a1 -> a2) -> [] a1 -> [] a2
map f s =
  case s of
    [] -> []
    (:) x s' -> (:) (f x) (Tree.map f s')

path :: Rel a1 -> a1 -> [] a1 -> Prelude.Bool
path e x p =
  case p of
    [] -> Prelude.True
    (:) y p' -> (Prelude.&&) (e x y) (path e y p')

sorted :: Rel a1 -> [] a1 -> Prelude.Bool
sorted leT s =
  case s of
    [] -> Prelude.True
    (:) x s' -> path leT x s'

bind :: (a1 -> Prelude.Maybe a2) -> Prelude.Maybe a1 -> Prelude.Maybe a2
bind f x =
  case x of
    Prelude.Just x' -> f x'
    Prelude.Nothing -> Prelude.Nothing

true_some :: Prelude.Bool -> a1 -> Prelude.Maybe a1
true_some b f =
  case b of
    Prelude.True -> Prelude.Just f
    Prelude.False -> Prelude.Nothing

data Tree t = Node t ([] (Tree t))

value :: Tree a1 -> a1
value t0 =
  case t0 of
    Node v _ -> v

children :: Tree a1 -> [] (Tree a1)
children t0 =
  case t0 of
    Node _ cs -> cs

find :: (a1 -> Prelude.Bool) -> [] a1 -> Prelude.Maybe a1
find p xs =
  case xs of
    [] -> Prelude.Nothing
    (:) xh xt ->
      case p xh of
        Prelude.True -> Prelude.Just xh
        Prelude.False -> find p xt

seqminus :: Type -> [] Sort -> [] Sort -> [] Sort
seqminus x x0 y =
  filter
    ( \z ->
        Prelude.not (in_mem z (mem (seq_predType x) (unsafeCoerce y)))
    )
    x0

g_insert :: Type -> Rel Sort -> Sort -> [] Sort -> [] Sort
g_insert x r0 x0 xs =
  case xs of
    [] -> [x0]
    (:) xh xt ->
      case eq_op x x0 xh of
        Prelude.True -> xs
        Prelude.False ->
          case r0 x0 xh of
            Prelude.True -> (:) x0 xs
            Prelude.False -> (:) xh (g_insert x r0 x0 xt)

is_tree_sorted :: Type -> Rel Sort -> Tree Sort -> Prelude.Bool
is_tree_sorted t0 r0 t1 =
  case t1 of
    Node _ cs ->
      (Prelude.&&) (sorted r0 (Tree.map value cs)) (Tree.all (is_tree_sorted t0 r0) cs)

type Sorted_tree =
  Tree Sort

-- singleton inductive, whose constructor was STree

treeOf :: Type -> Rel Sort -> Sorted_tree -> Tree Sort
treeOf _ _ s =
  s

sNode :: Type -> Rel Sort -> Sort -> Sorted_tree
sNode _ _ t0 =
  Node t0 []

treeR :: Type -> Rel Sort -> Tree Sort -> Tree Sort -> Prelude.Bool
treeR _ r0 x y =
  r0 (value x) (value y)

by_value :: Type -> Sort -> Tree Sort -> Prelude.Bool
by_value t0 v =
  funcomp () (eq_op t0 v) value

without :: Type -> Sort -> [] (Tree Sort) -> [] (Tree Sort)
without t0 v =
  filter (funcomp () Prelude.not (by_value t0 v))

without' :: Type -> Sort -> [] (Tree Sort) -> [] (Tree Sort)
without' t0 =
  locked (without t0)
