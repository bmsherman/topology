import Test

toInt :: Nat -> Int
toInt O = 0
toInt (S n) = 1 + toInt n

fromInt :: Int -> Nat
fromInt n | n < 0 = error "nat must be at least 0"
fromInt 0 = O
fromInt n = S (fromInt (n - 1))

instance Show Nat where
  show = show . toInt
