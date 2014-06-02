open import Level using (Level; suc; zero; _⊔_)
open import Function using (const)
open import Algebra
open import Algebra.Structures
open import Algebra.OrderedMonoid
open import Algebra.FunctionProperties as FunctionProperties using (Op₁; Op₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary
open import Relation.Binary.PartialOrderReasoning as ≤-Reasoning using ()

module Algebra.Pregroup where


-- Definition of the properties of left and right contraction and
-- expansion for usage in the below definition of pregroups.
module AdjointProperties {a ℓ} {A : Set a} (_≤_ : Rel A ℓ) (_∙_ : Op₂ A) (ε : A) where

  LeftContract : Op₁ A → Set _
  LeftContract _ˡ = ∀ x → (x ˡ ∙ x) ≤ ε

  LeftExpand : Op₁ A → Set _
  LeftExpand _ˡ = ∀ x → ε ≤ (x ∙ x ˡ)

  RightContract : Op₁ A → Set _
  RightContract _ʳ = ∀ x → (x ∙ x ʳ) ≤ ε

  RightExpand : Op₁ A → Set _
  RightExpand _ʳ = ∀ x → ε ≤ (x ʳ ∙ x)

  -- define shorthand notation for a term being the left/right adjoint
  -- of another term, which can be proven to be unique.
  _LeftAdjointOf_ : ∀ y x → Set _
  _LeftAdjointOf_ y x = (y ∙ x) ≤ ε × ε ≤ (x ∙ y)

  _RightAdjointOf_ : ∀ y x → Set _
  _RightAdjointOf_ y x = (x ∙ y) ≤ ε × ε ≤ (y ∙ x)


-- Definition of a pregroup, which adds a left and a right adjoint to
-- an ordered monoid.
record IsPregroup {a ℓ₁ ℓ₂} {A : Set a} (≈ : Rel A ℓ₁) (≤ : Rel A ℓ₂)
                  (∙ : Op₂ A) (ε : A) (ˡ : Op₁ A) (ʳ : Op₁ A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where

  open AdjointProperties ≤ ∙ ε
  field
    isOrderedMonoid : IsOrderedMonoid ≈ ≤ ∙ ε
    ˡ-cong          : ˡ Preserves ≈ ⟶ ≈
    ʳ-cong          : ʳ Preserves ≈ ⟶ ≈
    ˡ-contract      : LeftContract ˡ
    ˡ-expand        : LeftExpand ˡ
    ʳ-contract      : RightContract ʳ
    ʳ-expand        : RightExpand ʳ

  open IsOrderedMonoid isOrderedMonoid public
  open AdjointProperties ≤ ∙ ε public

record Pregroup c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infixl 7 _∙_
  infix  4 _≈_
  infix  4 _≤_
  field
    Carrier    : Set c
    _≈_        : Rel Carrier ℓ₁
    _≤_        : Rel Carrier ℓ₂
    _∙_        : Op₂ Carrier
    _ˡ         : Op₁ Carrier
    _ʳ         : Op₁ Carrier
    ε          : Carrier
    isPregroup : IsPregroup _≈_ _≤_ _∙_ ε _ˡ _ʳ

  open IsPregroup isPregroup public

  private
    -- for usage with ≤-Reasoning
    poset : Poset c ℓ₁ ℓ₂
    poset = record { isPartialOrder = isPartialOrder }
    open ≤-Reasoning poset

    -- for usage of substitutivity (which is not defined in IsPregroup)
    orderedMonoid : OrderedMonoid _ _ _
    orderedMonoid = record { isOrderedMonoid = isOrderedMonoid }
    open OrderedMonoid orderedMonoid public using (substitutivity)

  ˡ-unique : ∀ {x y} → y LeftAdjointOf x → y ≈ x ˡ
  ˡ-unique {x} {y} (y-contract , y-expand) = antisym y≤xˡ xˡ≤y
    where
      y≤xˡ : y ≤ x ˡ
      y≤xˡ =
        begin
          y             ≈⟨ sym (proj₂ identity y) ⟩
          y ∙ ε         ≤⟨ compatibility ≤-refl (ˡ-expand x) ⟩
          y ∙ (x ∙ x ˡ) ≈⟨ sym (assoc y x (x ˡ)) ⟩
          (y ∙ x) ∙ x ˡ ≤⟨ compatibility y-contract ≤-refl ⟩
          ε ∙ x ˡ       ≈⟨ proj₁ identity (x ˡ) ⟩
          x ˡ
        ∎
      xˡ≤y : x ˡ ≤ y
      xˡ≤y =
        begin
          x ˡ             ≈⟨ sym (proj₂ identity (x ˡ)) ⟩
          x ˡ ∙ ε         ≤⟨ compatibility ≤-refl y-expand ⟩
          x ˡ ∙ (x ∙ y)   ≈⟨ sym (assoc (x ˡ) x y) ⟩
          (x ˡ  ∙ x) ∙ y  ≤⟨ compatibility (ˡ-contract x) ≤-refl ⟩
          ε ∙ y           ≈⟨ proj₁ identity y ⟩
          y
        ∎

  ʳ-unique : ∀ {x y} → y RightAdjointOf x → y ≈ x ʳ
  ʳ-unique {x} {y} (y-contract , y-expand) = antisym y≤xʳ xʳ≤y
    where
      xʳ≤y : x ʳ ≤ y
      xʳ≤y =
        begin
          x ʳ             ≈⟨ sym (proj₁ identity (x ʳ)) ⟩
          ε ∙ x ʳ         ≤⟨ compatibility y-expand ≤-refl ⟩
          (y ∙ x) ∙ x ʳ ≈⟨ assoc  y x (x ʳ) ⟩
          y ∙ (x ∙ x ʳ) ≤⟨ compatibility ≤-refl (ʳ-contract x) ⟩
          y ∙ ε         ≈⟨ proj₂ identity y ⟩
          y
        ∎
      y≤xʳ : y ≤ x ʳ
      y≤xʳ =
        begin
          y             ≈⟨ sym (proj₁ identity y) ⟩
          ε ∙ y         ≤⟨ compatibility (ʳ-expand x) ≤-refl ⟩
          (x ʳ ∙ x) ∙ y ≈⟨ assoc (x ʳ) x y ⟩
          x ʳ ∙ (x ∙ y) ≤⟨ compatibility ≤-refl y-contract ⟩
          x ʳ ∙ ε       ≈⟨ proj₂ identity (x ʳ) ⟩
          x ʳ
        ∎


  ˡ-identity : ε ˡ ≈ ε
  ˡ-identity = antisym εˡ≤ε ε≤εˡ
    where
      εˡ≤ε : ε ˡ ≤ ε
      εˡ≤ε =
        begin
          ε ˡ     ≈⟨ sym (proj₂ identity (ε ˡ)) ⟩
          ε ˡ ∙ ε ≤⟨ ˡ-contract ε ⟩
          ε
        ∎
      ε≤εˡ : ε ≤ ε ˡ
      ε≤εˡ =
        begin
          ε       ≤⟨ ˡ-expand ε ⟩
          ε ∙ ε ˡ ≈⟨ proj₁ identity (ε ˡ) ⟩
          ε ˡ
        ∎

  ʳ-identity : ε ʳ ≈ ε
  ʳ-identity = antisym εʳ≤ε ε≤εʳ
    where
      εʳ≤ε : ε ʳ ≤ ε
      εʳ≤ε =
        begin
          ε ʳ     ≈⟨ sym (proj₁ identity (ε ʳ)) ⟩
          ε ∙ ε ʳ ≤⟨ ʳ-contract ε ⟩
          ε
        ∎
      ε≤εʳ : ε ≤ ε ʳ
      ε≤εʳ =
        begin
          ε       ≤⟨ ʳ-expand ε ⟩
          ε ʳ ∙ ε ≈⟨ proj₂ identity (ε ʳ) ⟩
          ε ʳ
        ∎

  ˡ-distrib : ∀ x y → y ˡ ∙ x ˡ ≈ (x ∙ y) ˡ
  ˡ-distrib x y = ˡ-unique ([yˡxˡ][xy]≤ε , ε≤[xy][yˡxˡ])
    where
      [yˡxˡ][xy]≤ε : (y ˡ ∙ x ˡ) ∙ (x ∙ y) ≤ ε
      [yˡxˡ][xy]≤ε =
        begin
          (y ˡ ∙ x ˡ) ∙ (x ∙ y) ≈⟨ sym (assoc (y ˡ ∙ x ˡ) x y) ⟩
          ((y ˡ ∙ x ˡ) ∙ x) ∙ y ≈⟨ ∙-cong (assoc (y ˡ) (x ˡ) x) refl ⟩
          (y ˡ ∙ (x ˡ ∙ x)) ∙ y ≤⟨ compatibility (compatibility ≤-refl (ˡ-contract x)) ≤-refl ⟩
          y ˡ ∙ ε ∙ y           ≈⟨ ∙-cong (proj₂ identity (y ˡ)) refl ⟩
          y ˡ ∙ y               ≤⟨ ˡ-contract y ⟩
          ε
        ∎
      ε≤[xy][yˡxˡ] : ε ≤ (x ∙ y) ∙ (y ˡ ∙ x ˡ)
      ε≤[xy][yˡxˡ] =
        begin
          ε                     ≤⟨ ˡ-expand x ⟩
          x ∙ x ˡ               ≈⟨ ∙-cong (sym (proj₂ identity x)) refl ⟩
          x ∙ ε ∙ x ˡ           ≤⟨ compatibility (compatibility ≤-refl (ˡ-expand y)) ≤-refl ⟩
          (x ∙ (y ∙ y ˡ) ∙ x ˡ) ≈⟨ ∙-cong (sym (assoc x y (y ˡ))) refl ⟩
          ((x ∙ y) ∙ y ˡ) ∙ x ˡ ≈⟨ assoc (x ∙ y) (y ˡ) (x ˡ) ⟩
          (x ∙ y) ∙ (y ˡ ∙ x ˡ)
        ∎

  ʳ-distrib : ∀ x y → y ʳ ∙ x ʳ ≈ (x ∙ y) ʳ
  ʳ-distrib x y = ʳ-unique ([xy][yʳxʳ]≤ε , ε≤[xy][yʳxʳ])
    where
      [xy][yʳxʳ]≤ε : (x ∙ y) ∙ (y ʳ ∙ x ʳ) ≤ ε
      [xy][yʳxʳ]≤ε =
        begin
          (x ∙ y) ∙ (y ʳ ∙ x ʳ) ≈⟨ sym (assoc (x ∙ y) (y ʳ) (x ʳ)) ⟩
          ((x ∙ y) ∙ y ʳ) ∙ x ʳ ≈⟨ ∙-cong (assoc x y (y ʳ)) refl ⟩
          (x ∙ (y ∙ y ʳ) ∙ x ʳ) ≤⟨ compatibility (compatibility ≤-refl (ʳ-contract y)) ≤-refl ⟩
          x ∙ ε ∙ x ʳ           ≈⟨ ∙-cong (proj₂ identity x) refl ⟩
          x ∙ x ʳ               ≤⟨ ʳ-contract x ⟩
          ε
        ∎
      ε≤[xy][yʳxʳ] : ε ≤ (y ʳ ∙ x ʳ) ∙ (x ∙ y)
      ε≤[xy][yʳxʳ] =
        begin
          ε                     ≤⟨ ʳ-expand y ⟩
          y ʳ ∙ y               ≈⟨ ∙-cong refl (sym (proj₁ identity y)) ⟩
          y ʳ ∙ (ε ∙ y)         ≤⟨ compatibility ≤-refl (compatibility (ʳ-expand x) ≤-refl) ⟩
          y ʳ ∙ ((x ʳ ∙ x) ∙ y) ≈⟨ ∙-cong refl (assoc (x ʳ) x y) ⟩
          y ʳ ∙ (x ʳ ∙ (x ∙ y)) ≈⟨ sym (assoc (y ʳ) (x ʳ) (x ∙ y)) ⟩
          (y ʳ ∙ x ʳ) ∙ (x ∙ y)
        ∎

  ˡ-contra : ∀ {x y} → x ≤ y → y ˡ ≤ x ˡ
  ˡ-contra {x} {y} x≤y =
    begin
      y ˡ             ≈⟨ sym (proj₂ identity (y ˡ)) ⟩
      y ˡ ∙ ε         ≤⟨ compatibility ≤-refl (ˡ-expand x) ⟩
      y ˡ ∙ (x ∙ x ˡ) ≈⟨ sym (assoc (y ˡ) x (x ˡ)) ⟩
      (y ˡ ∙ x) ∙ x ˡ ≤⟨ substitutivity x≤y ⟩
      (y ˡ ∙ y) ∙ x ˡ ≤⟨ compatibility (ˡ-contract y) ≤-refl ⟩
      ε ∙ x ˡ         ≈⟨ proj₁ identity (x ˡ) ⟩
      x ˡ
    ∎

  ʳ-contra : ∀ {x y} → x ≤ y → y ʳ ≤ x ʳ
  ʳ-contra {x} {y} x≤y =
    begin
      y ʳ             ≈⟨ sym (proj₁ identity (y ʳ)) ⟩
      ε ∙ y ʳ         ≤⟨ compatibility (ʳ-expand x) ≤-refl ⟩
      (x ʳ ∙ x) ∙ y ʳ ≤⟨ substitutivity x≤y ⟩
      (x ʳ ∙ y) ∙ y ʳ ≈⟨ assoc (x ʳ) y (y ʳ) ⟩
      x ʳ ∙ (y ∙ y ʳ) ≤⟨ compatibility ≤-refl (ʳ-contract y) ⟩
      x ʳ ∙ ε         ≈⟨ proj₂ identity (x ʳ) ⟩
      x ʳ
    ∎

  ʳˡ-cancel : ∀ x → x ʳ ˡ ≈ x
  ʳˡ-cancel x = sym (ˡ-unique (ʳ-contract x , ʳ-expand x))

  ˡʳ-cancel : ∀ x → x ˡ ʳ ≈ x
  ˡʳ-cancel x = sym (ʳ-unique (ˡ-contract x , ˡ-expand x))
