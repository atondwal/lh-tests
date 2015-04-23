{-@ data Node v = Leaf v | Node (r :: Node {a:v|a<c} ) (c :: v) (l :: Node {a:v|a>c} ) @-}

data Node v = Leaf v | Node (Node v) v (Node v)

{-@ measure height @-}
height :: Node a -> Integer
height (Leaf _) = 1
height (Node r _ l) = if ρ > λ then ρ else λ
        where ρ = 1 + height r
              λ = 1 + height l

{-@ measure balanced @-}
balanced :: Node a -> Bool
balanced (Leaf _) = True
balanced (Node r _ l) = balanced r && balanced l && (height r) - (height l) <= 1 && (height r) - (height l) >= -1

{-@ testTreeEven :: {v : Node Integer | balanced v} @-}
testTreeEven :: Node Integer
testTreeEven = Node (Leaf 1) 2 (Leaf 3)

{-@ testTreeLeft :: {v : Node Integer | balanced v} @-}
testTreeLeft :: Node Integer
testTreeLeft = Node (Node (Leaf 0) 1 (Leaf 3)) 2 (Leaf 3)

{-@ testTreeRight :: {v : Node Integer | balanced v} @-}
testTreeRight :: Node Integer
testTreeRight = Node (Leaf 3) 2 (Node (Leaf 0) 1 (Leaf 3))

{-@ testTreeBroke :: {v : Node Integer | balanced v} @-}
testTreeBroke :: Node Integer
testTreeBroke = Node (Node (Node (Leaf 0) 1 (Leaf 3)) 3 (Node (Leaf 0) 1 (Leaf 3))) 1 (Leaf 3)
