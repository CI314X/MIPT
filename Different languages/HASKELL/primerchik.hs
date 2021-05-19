factorial 0=1
factorial n|n<0 = error "Stupid"
           |n>=0 = n*factorial(n-1)

(~=) x y = abs(x-y)<0.001

data Pair a b = Pair a b

solve :: Double -> Double -> Maybe Double
solve 0 b = Nothing
solve a b = Just (-b/a)

data Color = Red | Green | Blue | RGB Int Int Int

data Tree a = Leaf a
             | Branch (Tree a)(Tree a)

treeSize (Leaf _) = 1
treeSize (Branch l r) = treeSize l + treeSize r

leafList :: Tree a->[a]
leafList (Leaf x)=[x]
leafList (Branch l r) = leafList l ++ leafList r

data List a = Nil | Cons a (List a)

headList (Cons x _)=x
headList Nil = error "headList : empty list"
tailList (Cons _ y)=y
tailList Nil = error "tailList : empty list"

data Expr = Const Integer
           |Add Expr Expr
           |Mult Expr Expr
           |Var String

eval::Expr -> Integer
eval (Const x)=x
eval (Add x y) = eval x + eval y
eval (Mult x y) = eval x * eval y

diff::Expr -> Expr
diff (Const _) = Const 0
diff (Var x) = Const 1
diff (Add x y) = Add (diff x)(diff y)
diff (Mult x y) = Add (Mult (diff x) y )(Mult x (diff y))


transformList f [] = []
transfromList f (x:xs) = f x :transformList f xs

sqrtList  = transfromList sqrt 

isPositive x = x>0
getPositive = filter isPositive

multList []=1
multList (x:xs) = x*multList xs



