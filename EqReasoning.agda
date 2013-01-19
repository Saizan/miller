module EqReasoning where

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
import Relation.Binary.HeterogeneousEquality as H
open H using (_≅_)
import Relation.Binary.EqReasoning as EqR

open EqR public using () renaming (begin_ to begin[_]_)

module _ {s₁ s₂} {S : Setoid s₁ s₂} where
  open EqR S public
      hiding (begin_)

  infixr 2 _≅⟨_⟩_

  _≅⟨_⟩_ : (x : _) {y z : _} →
           x ≅ y → y IsRelatedTo z → x IsRelatedTo z
  _ ≅⟨ x≅y ⟩ y≡z = _ ≡⟨ H.≅-to-≡ x≅y ⟩ y≡z

module _ {a} {A : Set a} where
  open EqR (setoid A) public
      using (begin_)

