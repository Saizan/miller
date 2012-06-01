module Lists where


open import Data.List public using (List; []; _∷_)
{-
data Fwd (X : Set) : Set where
  !> : Fwd X
  _:>_ : X → Fwd X → Fwd X
-}
Fwd : Set → Set
Fwd = List

pattern !> = []
pattern _:>_ x xs = x ∷ xs

infixr 50 _:>_

{-
data Bwd (X : Set) : Set where
  <! : Bwd X
  _<:_ : Bwd X → X → Bwd X
-}
Bwd : Set →  Set
Bwd = List
pattern <! = []
pattern _<:_ xs x = x ∷ xs
infixl 30 _<:_
