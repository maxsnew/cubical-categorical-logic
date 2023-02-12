{-# OPTIONS --rewriting #-}

module Multicategory.Planar where

open import Cubical.Foundations.Prelude

open import Context
private
  variable
    ℓo ℓh ℓ ℓ' ℓ'' : Level

record Multicategory ℓo ℓh : Type (ℓ-suc (ℓ-max ℓo ℓh)) where
  field
    Ob  : Type ℓo
    Hom : Ctx Ob → Ob → Type ℓh
    id      : ∀ (A : Ob) → Hom (sole A) A
    _∘[_]_ : ∀ {Γ Δ A} → Hom Γ A → (x : Var Γ) → Hom Δ (Γ [ x ]) → Hom (Γ [ Δ / x ]) A
    idR    : ∀ {Γ A} → (M : Hom Γ A) → (x : Var Γ)
           → PathP (λ i → Hom (sole-/R Γ x i) A) (M ∘[ x ] (id (Γ [ x ]))) M
    -- idL    : ∀ {Γ A} → (M : Hom Γ A)
    --        → PathP (λ i → Hom (sole-/L A Γ i) A) (id A ∘[ the-var A ] M) M
    -- compAssoc : ∀ {Γ₁ Γ₂ Γ₃ A}
    --           → (M : Hom Γ₁ A) 
    --           → (x : Var Γ₁) → (N : Hom Γ₂ (Γ₁ [ x ]))
    --           → (y : Var Γ₂) → (P : Hom Γ₃ (Γ₂ [ y ]))
    --           → PathP ? (M ∘[ x ] (N ∘[ y ] P)) ≡ (M ∘[ x ] N) ∘[ nest-var Γ₁ Γ₂ x y ] P
