{-@ data Node v = Leaf v | Node (c :: v) (r :: Node {a:v|a<c} ) (l :: Node {a:v|a>c} ) @-}

data Node v = Leaf v | Node v (Node v) (Node v)

{-@ measure height @-}
height :: Node a -> Integer
height (Leaf _) = 1
height (Node _ r l) = if ρ > λ then ρ else λ
        where ρ = 1 + height r
              λ = 1 + height l

{-@ measure balanced @-}
balanced :: Node a -> Bool
balanced (Leaf _) = True
balanced (Node _ r l) = balanced r && balanced l && (height r) - (height l) <= 1 && (height r) - (height l) >= -1

{-@ testTreeEven :: {v : Node Integer | balanced v} @-}
testTreeEven :: Node Integer
testTreeEven = Node 2 (Leaf 1) (Leaf 3)

{-@ testTreeLeft :: {v : Node Integer | balanced v} @-}
testTreeLeft :: Node Integer
testTreeLeft = Node 2 (Node 1 (Leaf 3) (Leaf 0)) (Leaf 3)

{-@ testTreeRight :: {v : Node Integer | balanced v} @-}
testTreeRight :: Node Integer
testTreeRight = Node 1 (Leaf 3) (Node 2 (Leaf 0) (Leaf 3))

{-@ testTreeBroke :: {v : Node Integer | balanced v} @-}
testTreeBroke :: Node Integer
testTreeBroke = Node 1 (Node 1 (Leaf 3) (Node 1 (Leaf 0) (Leaf 3))) (Node 3 (Leaf 0) (Leaf 3))
