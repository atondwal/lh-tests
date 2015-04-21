data Balance = R | L | C

{-@ data Node v <p :: Bool -> v -> v -> Prop> = Leaf v | Node Balance (r :: Node <p> v<p True c>) (c :: v) (l :: Node <p> v<p False c>) @-}

data Node v = Leaf v | Node Balance (Node v) v (Node v)

{-@ measure height @-}
height :: Node a -> Integer
height (Leaf _) = 1
height (Node _ r _ l) = 1 + (max (height r) (height l))

{-@ measure balanced @-}
balanced :: Node a -> Bool
balanced (Leaf _) = True
balanced (Node R r _ l) = balanced r && balanced l && height r == 1+height l
balanced (Node L r _ l) = balanced r && balanced l && height l == 1+height r
balanced (Node C r _ l) = balanced r && balanced l && height l == height r


{-@ type BST a = Node <{\b v n -> (n<=v) <=> b==True}> a @-}

{-@ testTree :: BST Integer @-}
testTree :: Node Integer
testTree = Node C (Leaf 1) 2 (Leaf 3)

{-@ testTree2 :: BST Integer @-}
testTree2 :: Node Integer
testTree2 = Node C (Leaf 5) 2 (Leaf 3)
