open import Level using (Level; suc; zero; _⊔_)
open import Function using (const)
open import Algebra
open import Algebra.Structures
open import Algebra.OrderedMonoid
open import Algebra.Pregroup
open import Algebra.FunctionProperties as FunctionProperties using (Op₁; Op₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary
open import Relation.Binary.PartialOrderReasoning as ≤-Reasoning using ()

module Algebra.PregroupPlus where

record IsPregroupPlus
       {a ℓ₁ ℓ₂} {A : Set a} (≈ : Rel A ℓ₁) (≤ : Rel A ℓ₂)
       (∙ : Op₂ A) (ε₁ : A) (ˡ : Op₁ A) (ʳ : Op₁ A)
       (+ : Op₂ A) (ε₀ : A) (ᵘ : Op₁ A) (ᵈ : Op₁ A)
       : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where

  field
    ∙-isPregroup : IsPregroup ≈ ≤ ∙ ε₁ ˡ ʳ
    +-isPregroup : IsPregroup ≈ ≤ + ε₀ ᵘ ᵈ

  open IsPregroup ∙-isPregroup public
       using (ˡ-cong; ʳ-cong; ˡ-contract; ʳ-contract
             ;ˡ-expand; ʳ-expand; ∙-cong)
       renaming (assoc to ∙-assoc; identity to ∙-identity
                ;compatibility to ∙-compatibility)
  open IsPregroup +-isPregroup public
       using (≤-refl; ≤-reflexive; ≤-trans; ≤-resp-≈; refl; sym; trans; antisym)
       renaming (ˡ-cong to ᵈ-cong; ʳ-cong to ᵘ-cong
                ;ˡ-contract to ᵈ-contract; ʳ-contract to ᵘ-contract
                ;ˡ-expand to ᵈ-expand; ʳ-expand to ᵘ-expand
                ;∙-cong to +-cong; assoc to +-assoc; identity to +-identity
                ;compatibility to +-compatibility)


record PregroupPlus c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infixl 7 _∙_
  infixl 6 _+_
  infix  4 _≈_
  infix  4 _≤_
  field
    Carrier         : Set c
    _≈_             : Rel Carrier ℓ₁
    _≤_             : Rel Carrier ℓ₂
    _∙_             : Op₂ Carrier
    ε₁              : Carrier
    _ˡ              : Op₁ Carrier
    _ʳ              : Op₁ Carrier
    _+_             : Op₂ Carrier
    ε₀              : Carrier
    _ᵘ              : Op₁ Carrier
    _ᵈ              : Op₁ Carrier
    isPregroupPlus  : IsPregroupPlus _≈_ _≤_ _∙_ ε₁ _ˡ _ʳ _+_ ε₀ _ᵘ _ᵈ

  open IsPregroupPlus isPregroupPlus public

  ∙-pregroup : Pregroup _ _ _
  ∙-pregroup = record { isPregroup = ∙-isPregroup }
  open Pregroup ∙-pregroup public using (
    ˡ-unique; ˡ-identity; ˡ-distrib; ˡ-contra; ˡʳ-cancel;
    ʳ-unique; ʳ-identity; ʳ-distrib; ʳ-contra; ʳˡ-cancel)

  +-pregroup : Pregroup _ _ _
  +-pregroup = record { isPregroup = +-isPregroup }
  open Pregroup +-pregroup public using () renaming (
    ˡ-unique to ᵈ-unique; ˡ-identity to ᵈ-identity; ˡ-distrib to ᵈ-distrib;
    ˡ-contra to ᵈ-contra; ˡʳ-cancel to ᵈᵘ-cancel;
    ʳ-unique to ᵘ-unique; ʳ-identity to ᵘ-identity; ʳ-distrib to ᵘ-distrib;
    ʳ-contra to ᵘ-contra; ʳˡ-cancel to ᵘᵈ-calcel)

  xˡᵘʳᵈ≈x : ∀ x → x ˡ ᵘ ʳ ᵈ ≈ x
  xˡᵘʳᵈ≈x x = {!!}
