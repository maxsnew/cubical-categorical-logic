{-# OPTIONS --safe #-}

module AltEquationalReasoning where

open import Cubical.Foundations.Prelude hiding (≡⟨⟩-syntax; _∎; _≡⟨_⟩_)

private
  variable
    ℓ ℓ' : Level

≡⟨⟩-syntax : ∀ {ℓ} {A : Type ℓ} (x : A) {y z} → y ≡ z → x ≡ y → x ≡ z
≡⟨⟩-syntax x q p = p ∙ q

infixr 2 ≡⟨⟩-syntax

syntax ≡⟨⟩-syntax x q p = x ≡⟨ p ⟩ q

-- infix  3 _∎
-- _∎ : ∀ {ℓ} {A : Type ℓ} (x : A) → x ≡ x
-- x ∎ = refl
