{-@ data Node v <p :: Bool -> v -> v -> Prop> = Leaf | Node (r :: Node <p> v<p True c>) (c :: v) (l :: Node <p> v<p False c>) @-}

data Node v = Leaf | Node (Node v) v (Node v)

{-@ measure height @-}
height :: Node a -> Integer
height Leaf = 0
height (Node r _ l) = if ρ > λ then ρ else λ
        where ρ = 1 + height r
              λ = 1 + height l

{-@ measure balanced @-}
balanced :: Node a -> Bool
balanced Leaf = True
balanced (Node r _ l) = balanced r && balanced l && (height r) - (height l) <= 1 && (height r) - (height l) >= -1

{-@ testTreeEven :: {v : Node Integer | balanced v} @-}
testTreeEven :: Node Integer
testTreeEven = Node Leaf 2 Leaf

{-@ type BST a = Node <{\b v n -> (n<=v) <=> b==True}> a @-}
{-@ testTreeLeft :: {v : Node Integer | balanced v} @-}
testTreeLeft :: Node Integer
testTreeLeft = Node (Node Leaf 1 Leaf) 2 Leaf

{-@ testTreeRight :: {v : Node Integer | balanced v} @-}
testTreeRight :: Node Integer
testTreeRight = Node Leaf 2 (Node Leaf 1 Leaf)

{-@ testTreeBroke :: {v : Node Integer | balanced v} @-}
testTreeBroke :: Node Integer
testTreeBroke = Node (Node (Node Leaf 1 Leaf) 3 (Node Leaf 1 Leaf)) 1 Leaf
