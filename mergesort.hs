{-@ type IncrList a = [a]<{\xi xj -> xi <= xj}> @-}

{-@ mergesort :: (Ord a) => [a] -> IncrList a @-}
mergesort :: Ord a => [a] -> [a]
mergesort l = uncurry conquer $ divide l

{-@ conquer :: (Ord a) => IncrList a -> IncrList a -> IncrList a @-}
conquer :: Ord a => [a] -> [a] -> [a]
conquer [] [] = []
conquer [x] [] = [x]
conquer [] [y] = [y]
conquer (x:xs) (y:ys) = if x>y then x:conquer xs (y:ys) else y:conquer (x:xs) ys

{-@ divide :: (Ord a) => [a] -> (IncrList a, IncrList a) @-}
divide :: Ord a => [a] -> ([a],[a])
divide l = (mergesort xs, mergesort ys)
  where (xs,ys) =  split l
        split [] = ([],[])
        split [a] = ([a],[])
        split (x:y:zs) = (x:χs,y:ηs)
          where (χs,ηs) = split zs

