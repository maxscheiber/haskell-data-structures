module AVL (
  AVL,
  empty,
  isEmpty,
  size,
  member,
  insert,
  delete,
  elems
) where
import Control.Monad
import Data.List(nub, sort)
import Test.QuickCheck

data AVL t =
  Empty
  | Node Int Int (AVL t) t (AVL t)
  deriving (Eq, Show)

empty :: AVL t
empty = Empty

node :: AVL t -> t -> AVL t -> AVL t
node l v r = 
  let bf = height l - height r in
  let ht = 1 + max (height l) (height r) in
  Node bf ht l v r

isEmpty :: AVL t -> Bool
isEmpty Empty = True
isEmpty _     = False

height :: AVL t -> Int
height Empty            = -1
height (Node _ h _ _ _) = h

size :: AVL t -> Int
size t = aux t 0 where
  aux Empty acc = acc
  aux (Node _ _ l _ r) acc = aux l (1 + aux r acc)

member :: Ord t => t -> AVL t -> Bool
member _ Empty = False
member tgt (Node _ _ l v r)
  | tgt < v   = member tgt l
  | tgt > v   = member tgt r
  | otherwise = True

-- http://en.wikipedia.org/wiki/AVL_tree#Insertion
rotateLeft :: AVL t -> AVL t
rotateLeft (Node _ _ a v (Node _ _ b v_r c)) = node (node a v b) v_r c
rotateLeft t = t

rotateRight :: AVL t -> AVL t
rotateRight (Node _ _ (Node _ _ b v_l c) v d) = node b v_l (node c v d)
rotateRight t = t

rebalance :: AVL t -> AVL t
-- left-right
rebalance (Node 2 _ t@(Node (-1) _ _ _ _) v d) = rebalance $ node (rotateLeft t) v d
-- left-left
rebalance t@(Node 2 _ _ _ _) = rotateRight t
-- right-left
rebalance (Node (-2) _ a v t@(Node 1 _ _ _ _)) = rebalance $ node a v (rotateRight t)
-- right-right
rebalance t@(Node (-2) _ _ _ _) = rotateLeft t
-- already balanced
rebalance t = t

insert :: Ord t => t -> AVL t -> AVL t
insert x Empty = node Empty x Empty
insert x t@(Node _ _ l v r)
  | x < v     = rebalance $ node (insert x l) v r
  | x > v     = rebalance $ node l v (insert x r)
  | otherwise = t

delete :: Ord t => t -> AVL t -> AVL t
delete x Empty = Empty
delete x (Node _ _ l v r)
  | x < v     = rebalance $ node (delete x l) v r
  | x > v     = rebalance $ node l v (delete x r)
  | otherwise =
    case (l, r) of
      (Empty, Empty) -> Empty
      (_, Empty)     -> l
      (Empty, _)     -> r
      _ -> let m = treeMax l in rebalance $ node (delete m l) m r
  where treeMax Empty = error "Broken invariant: treeMax called on empty tree"
        treeMax (Node _ _ _ v Empty) = v
        treeMax (Node _ _ _ _ rt) = treeMax rt

elems :: AVL t -> [t]
elems t = aux t [] where
  aux Empty acc = acc
  aux (Node _ _ l v r) acc = aux l (v : aux r acc)

---------------
-- | Tests | --
---------------
instance (Ord t, Arbitrary t) => Arbitrary (AVL t) where
  arbitrary = liftM (foldr insert empty) arbitrary

-- | Consider the following AVL invariants.
-- 1. The height at each node is correctly calculated.
prop_ht_correct :: AVL Int -> Bool
prop_ht_correct Empty = height Empty == -1
prop_ht_correct t@(Node _ h l _ r) = 
  h == calcHt t && prop_ht_correct l && prop_ht_correct r
  where calcHt Empty = -1
        calcHt (Node _ _ l' _ r') = 1 + max (calcHt l') (calcHt r')

-- 2. The balance factor at each node is correctly calculated.
prop_bf_correct :: AVL Int -> Bool
prop_bf_correct Empty = True
prop_bf_correct t@(Node bf _ l _ r) =
  bf == calcBf t && prop_bf_correct l && prop_bf_correct r
  where calcBf Empty = 0
        calcBf (Node _ _ l' _ r') = height l' - height r'

-- 3. The balance factor at each node is between -1 and 1.
prop_balance :: AVL Int -> Bool
prop_balance Empty = True
prop_balance (Node bf _ l _ r) = abs bf <= 1 && prop_balance l && prop_balance r

-- 4. The items stored in the tree are in strictly increasing order.
prop_inorder :: AVL Int -> Bool
prop_inorder t =
  let xs = elems t in
  xs == (nub $ sort xs)

-- 5. The height is bounded by about 1.5log_2(n+2) - 0.328.
prop_height :: AVL Int -> Bool
prop_height t =
  let n = size t in
  let h = height t in
  fromIntegral h <= 1.44 * (logBase 2 (fromIntegral (n+2))) - 0.328

check :: AVL Int -> Bool
check t = prop_ht_correct t && prop_bf_correct t && prop_balance t && prop_inorder t && prop_height t

-- | Check that insertions work correctly.
prop_insert :: Int -> AVL Int -> Bool
prop_insert x t = 
  let t' = insert x t in
  check t' && allElem t t' && member x t'
  where allElem Empty _ = True
        allElem (Node _ _ l v r) t' = 
          member v t' && allElem l t' && allElem r t'

-- | Check that deletions work correctly.
prop_delete :: Int -> AVL Int -> Bool
prop_delete x t =
  let t' = delete x t in
  check t' && allElem t' t && not (member x t')
  where allElem Empty _ = True
        allElem (Node _ _ l v r) t' = 
          member v t' && allElem l t' && allElem r t'