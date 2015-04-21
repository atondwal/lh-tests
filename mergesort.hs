{-@ type IncrList a = [a]<{\xi xj -> xi <= xj}> @-}

{-@ mergesort :: (Ord a) => [a] -> IncrList a @-}
mergesort :: Ord a => [a] -> [a]
mergesort = (uncurry merge) . split

merge :: Ord a => [a] -> [a] -> [a]
merge [] [] = []
merge [x] [] = [x]
merge [] [y] = [y]
merge (x:xs) (y:ys) = if x>y then x:merge xs (y:ys) else y:merge (x:xs) ys

split :: Ord a => [a] -> ([a],[a])
split [] = ([],[])
split [a] = ([a],[])
split [a,b] = ([a],[b])
split (x:y:zs) = (mergesort (x:xs), mergesort (y:ys))
  where (xs,ys) = split zs
