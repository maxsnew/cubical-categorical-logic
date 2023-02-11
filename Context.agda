{-# OPTIONS --allow-unsolved-metas #-}
module Context where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Fin hiding (_/_)

private
  variable
    ℓ ℓ' ℓ'' : Level

record Ctx (A : Type ℓ) : Type ℓ where
  field
    len : ℕ
    elts : Fin len → A

Var : ∀ {A : Type ℓ} → Ctx A → Type
Var Θ = Fin (Ctx.len Θ)

sole : ∀ {A : Type ℓ} → A → Ctx A
sole a = record { len = 1 ; elts = λ _ → a }

the-var : ∀ {A : Type ℓ} → (a : A) → Var (sole a)
the-var a = zero , (zero , refl)

_[_] : ∀ {A : Type ℓ} → (Θ : Ctx A) → Var Θ → A
Θ [ x ] = Ctx.elts Θ x

-- if x : Var Θ, then len Θ = S n
-- so new len should be

-- split : ∀ m n → (Fin m) → Fin (predℕ m + n) ≡ 

_[_/_] : ∀ {A : Type ℓ} → (Θ : Ctx A) → Ctx A → Var Θ → Ctx A
Θ [ Υ / x ] = record { len = toℕ x + Ctx.len Υ + (Ctx.len Θ ∸ toℕ x) ; elts = {!!} }

sole-/ : ∀ {A : Type ℓ} → (Θ : Ctx A) → (x : Var Θ) → Θ [ sole (Θ [ x ]) / x ] ≡ Θ
sole-/ = {!!}

comp-/-/ : ∀ {A : Type ℓ} → (Θ₁ Θ₂ Θ₃ : Ctx A) → (i : Var Θ₁) (j : Var Θ₂) →
         Θ₁ [ (Θ₂ [ Θ₃ / j ]) / i ] ≡ ((Θ₁ [ Θ₂ / i ]) [ Θ₃ / {!i + j!} ])
comp-/-/ = {!!}
-- {-# REWRITE sole-/ comp-/-/ #-}


