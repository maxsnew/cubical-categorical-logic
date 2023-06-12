{-# OPTIONS --safe #-}

module AltEquationalReasoning where

open import Cubical.Foundations.Prelude hiding (≡⟨⟩-syntax; _∎; _≡⟨⟩_)

private
  variable
    ℓ ℓ' : Level

≡⟨⟩-syntax : ∀ {ℓ} {A : Type ℓ} (x : A) {y z} → y ≡ z → x ≡ y → x ≡ z
≡⟨⟩-syntax x q p = p ∙ q
≡i⟨⟩-syntax : ∀ {ℓ} {A : Type ℓ} (x : A) {y z} → y ≡ z → x ≡ y → x ≡ z
≡i⟨⟩-syntax = ≡⟨⟩-syntax

infixr 2 ≡⟨⟩-syntax ≡i⟨⟩-syntax
syntax ≡⟨⟩-syntax x q p = x ≡⟨ p ⟩ q
syntax ≡i⟨⟩-syntax x q (λ i → m)  = x ≡[ i ]⟨ m ⟩ q
