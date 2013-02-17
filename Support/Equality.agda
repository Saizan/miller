module Support.Equality where

open import Relation.Binary.PropositionalEquality public renaming ([_] to ⌞_⌟)
import Relation.Binary.HeterogeneousEquality
module Het = Relation.Binary.HeterogeneousEquality
open import Relation.Binary.HeterogeneousEquality public using (_≅_ ; _≇_ ; refl; ≅-to-≡; ≡-to-≅)
open import Data.Product

pattern refl` = (refl , refl)
