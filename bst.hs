{-@ data Node v = Nil | Node (c :: v) (r :: Node {a:v|a<c} ) (l :: Node {a:v|a>c} ) @-}

data Node v = Nil | Node v (Node v) (Node v)

{-@ measure height @-}
height :: Node a -> Integer
height Nil = 1
height (Node _ r l) = if ρ > λ then ρ else λ
        where ρ = 1 + height r
              λ = 1 + height l

{-@ measure balanced @-}
balanced :: Node a -> Bool
balanced Nil = True
balanced (Node _ r l) = balanced r && balanced l && (height r) - (height l) <= 1 && (height r) - (height l) >= -1

{-@ type AVL a = { v : Node a | balanced v} @-}

{-@ testTreeEven :: AVL Integer @-}
testTreeEven :: Node Integer
testTreeEven = Node 2 (Node 1 Nil Nil) (Node 3 Nil Nil)

{-@ testTreeLeft :: AVL Integer @-}
testTreeLeft :: Node Integer
testTreeLeft = Node 3 (Node 1 (Node 0 Nil Nil) (Node 2 Nil Nil)) (Node 4 Nil Nil)

{-@ testTreeRight :: AVL Integer @-}
testTreeRight :: Node Integer
testTreeRight = Node 0 (Node (-1) Nil Nil) (Node 2 (Node 1 Nil Nil) (Node 3 Nil Nil))

{-@ testTreeUnbal :: AVL Integer @-}
testTreeUnbal :: Node Integer
testTreeUnbal = Node 0 (Node (-5) (Node (-8) Nil Nil) (Node (-2) (Node (-3) Nil Nil) (Node (-1) Nil Nil))) (Node 1 Nil Nil)

{-@ testTreeUnsearch :: AVL Integer @-}
testTreeUnsearch :: Node Integer
testTreeUnsearch = Node 0 (Node 1 Nil Nil) (Node (-1) Nil Nil)
