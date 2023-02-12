{-# OPTIONS --allow-unsolved-metas --rewriting #-}
module Context where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sum
open import Cubical.Data.Fin hiding (_/_)

{-# BUILTIN REWRITE _≡_ #-}

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

lem1 : ∀ l m n → Fin (l + m + n) ≡ (Fin l ⊎ Fin m) ⊎ Fin n
lem1 l m n =
      Fin (l + m + n)           ≡⟨ Fin+≡Fin⊎Fin (l + m) n ⟩
      (Fin (l + m) ⊎ Fin n)     ≡⟨ (λ i → Fin+≡Fin⊎Fin l m i ⊎ Fin n) ⟩
      (Fin l ⊎ Fin m) ⊎ Fin n ∎ 

_[_/_] : ∀ {A : Type ℓ} → (Θ : Ctx A) → Ctx A → Var Θ → Ctx A
_[_/_] {A = A} Θ Υ x = record
      { len = toℕ x + Ctx.len Υ + (Ctx.len Θ ∸ (1 + toℕ x))
      ; elts = λ y → elts' (transport (lem1 (toℕ x) (Ctx.len Υ) (Ctx.len Θ ∸ (1 + toℕ x))) y)
      }
  where

    lem2 : ∀ l m n
         → m ≤ n
         → l < n ∸ m
         → l + m < n
    lem2 l m n m≤n l<n-m =
         l + m <≡⟨ ≤-+k l<n-m ⟩
         (n ∸ m) + m ≡⟨ ≤-∸-+-cancel m≤n ⟩
         n ∎
      where open <-Reasoning

    elts' : (Fin (toℕ x) ⊎ Fin (Ctx.len Υ)) ⊎ Fin (Ctx.len Θ ∸ (1 + toℕ x)) → A
    elts' (inl (inl y<x)) = Ctx.elts Θ ((toℕ y<x) , <-trans (snd y<x) (snd x))
    elts' (inl (inr y∈Υ)) = Ctx.elts Υ y∈Υ
    elts' (inr y>x) = Ctx.elts Θ ((toℕ y>x + (1 + toℕ x)) , lem2 (toℕ y>x) (1 + toℕ x) (Ctx.len Θ) (snd x) (snd y>x))

sole-/R : ∀ {A : Type ℓ} → (Θ : Ctx A) → (x : Var Θ) → Θ [ sole (Θ [ x ]) / x ] ≡ Θ
sole-/R Θ x = λ i → record { len = lem3 i ; elts = {!!} }
  where
    lem3 : Ctx.len (Θ [ sole (Θ [ x ]) / x ]) ≡ Ctx.len Θ
    lem3 =
      toℕ x + 1 + (Ctx.len Θ ∸ (1 + toℕ x)) ≡⟨ +-comm (toℕ x + 1) _ ⟩
      (Ctx.len Θ ∸ (1 + toℕ x)) + (toℕ x + 1) ≡⟨ (λ i → (Ctx.len Θ ∸ (1 + toℕ x)) + +-comm (toℕ x) 1 i) ⟩
      (Ctx.len Θ ∸ (1 + toℕ x)) + (1 + toℕ x) ≡⟨ ≤-∸-+-cancel (snd x) ⟩
      Ctx.len Θ ∎

    lem4 : Var (Θ [ sole (Θ [ x ]) / x ]) ≡ Var Θ
    lem4 = λ i → Fin (lem3 i)

    elts' : ∀ (y : Var (Θ [ sole (Θ [ x ]) / x ]))
          → Ctx.elts (Θ [ sole (Θ [ x ]) / x ]) y ≡ Ctx.elts Θ (transport lem4 y)
    elts' = {!!}
            

sole-/L : ∀ {A : Type ℓ} → (a : A) → (Θ : Ctx A) → sole a [ Θ / the-var a ] ≡ Θ
sole-/L = {!!}

-- comp-/-/ : ∀ {A : Type ℓ} → (Θ₁ Θ₂ Θ₃ : Ctx A) → (i : Var Θ₁) (j : Var Θ₂) →
--          Θ₁ [ (Θ₂ [ Θ₃ / j ]) / i ] ≡ ((Θ₁ [ Θ₂ / i ]) [ Θ₃ / {!i + j!} ])
-- comp-/-/ = {!!}

{-# REWRITE sole-/R #-}
-- {-# REWRITE sole-/L #-}
-- comp-/-/ too when I get it fixed
