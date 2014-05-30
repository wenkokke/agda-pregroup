open import Level using (Level; suc; zero; _⊔_)
open import Algebra.Structures
open import Algebra.FunctionProperties as FunctionProperties using (Op₁; Op₂)
open import Relation.Binary

-- Definition of an ordered monoid, which adds the law that ∙ must
-- preserve the partial order ≤ (or, equivalently, that an ordering x
-- ≤ y must allow for the substitution of y for x in a more complex
-- ordering) to an existing monoid and partial order.
module Algebra.OrderedMonoid where

record IsOrderedMonoid {a ℓ₁ ℓ₂} {A : Set a} (≈ : Rel A ℓ₁) (≤ : Rel A ℓ₂) (∙ : Op₂ A) (ε : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isMonoid       : IsMonoid ≈ ∙ ε
    isPartialOrder : IsPartialOrder ≈ ≤
    compatibility  : ∙ Preserves₂ ≤ ⟶ ≤ ⟶ ≤

  open IsMonoid isMonoid public
       hiding (isEquivalence)
  open IsPartialOrder isPartialOrder public
       renaming (refl to ≤-refl; trans to ≤-trans; reflexive to ≤-reflexive)

record OrderedMonoid c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infixl 7 _∙_
  infix  4 _≈_
  infix  4 _≤_
  field
    Carrier         : Set c
    _≈_             : Rel Carrier ℓ₁
    _≤_             : Rel Carrier ℓ₂
    _∙_             : Op₂ Carrier
    ε               : Carrier
    isOrderedMonoid : IsOrderedMonoid _≈_ _≤_ _∙_ ε

  open IsOrderedMonoid isOrderedMonoid public

  substitutivity : ∀ {x y z w} → x ≤ y → z ∙ x ∙ w ≤ z ∙ y ∙ w
  substitutivity x≤y = compatibility (compatibility ≤-refl x≤y) ≤-refl
