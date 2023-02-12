module Context where

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Empty as ⊥
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

finCases : ∀ l m n → Fin (l + m + n) → (Fin l ⊎ Fin m) ⊎ Fin n
finCases l m n x = map (Iso.fun (Fin+≅Fin⊎Fin l m)) (λ x → x) (Iso.fun (Fin+≅Fin⊎Fin (l + m) n) x)

-- More explicitly
-- finCases : ∀ l m n → Fin (l + m + n) → (Fin l ⊎ Fin m) ⊎ Fin n
-- finCases l m n x with Iso.fun (Fin+≅Fin⊎Fin (l + m) n) x
-- ... | inl x<l+m with Iso.fun (Fin+≅Fin⊎Fin l m) x<l+m
-- ... | inl x<l     = inl (inl x<l)
-- ... | inr m≤x<l+m = inl (inr m≤x<l+m)
-- finCases l m n x | inr x≥l+m = inr x≥l+m

lem2 : ∀ l m n
         → m ≤ n
         → l < n ∸ m
         → l + m < n
lem2 l m n m≤n l<n-m =
         l + m <≡⟨ ≤-+k l<n-m ⟩
         (n ∸ m) + m ≡⟨ ≤-∸-+-cancel m≤n ⟩
         n ∎
      where open <-Reasoning

_[_/_] : ∀ {A : Type ℓ} → (Θ : Ctx A) → Ctx A → Var Θ → Ctx A
_[_/_] {A = A} Θ Υ x = record
      { len = toℕ x + Ctx.len Υ + (Ctx.len Θ ∸ (1 + toℕ x))
      ; elts = λ y → elts' (finCases (toℕ x) (Ctx.len Υ) (Ctx.len Θ ∸ (1 + toℕ x)) y)
      }
  where

    elts' : (Fin (toℕ x) ⊎ Fin (Ctx.len Υ)) ⊎ Fin (Ctx.len Θ ∸ (1 + toℕ x)) → A
    elts' (inl (inl y<x)) = Ctx.elts Θ ((toℕ y<x) , <-trans (snd y<x) (snd x))
    elts' (inl (inr y∈Υ)) = Ctx.elts Υ y∈Υ
    elts' (inr y>x) = Ctx.elts Θ ((toℕ y>x + (1 + toℕ x)) , lem2 (toℕ y>x) (1 + toℕ x) (Ctx.len Θ) (snd x) (snd y>x))

sole-/R : ∀ {A : Type ℓ} → (Θ : Ctx A) → (x : Var Θ) → Θ [ sole (Θ [ x ]) / x ] ≡ Θ
sole-/R {A = A} Θ x @ (xN , x<lenΘ) = λ i → record { len = lem3 i ; elts = funExtDep elts' i }
  where
    lem3 : Ctx.len (Θ [ sole (Θ [ x ]) / x ]) ≡ Ctx.len Θ
    lem3 =
      xN + 1 + (Ctx.len Θ ∸ (1 + xN)) ≡⟨ +-comm (xN + 1) _ ⟩
      (Ctx.len Θ ∸ (1 + xN)) + (xN + 1) ≡⟨ (λ i → (Ctx.len Θ ∸ (1 + xN)) + +-comm (xN) 1 i) ⟩
      (Ctx.len Θ ∸ (1 + xN)) + (1 + xN) ≡⟨ ≤-∸-+-cancel (snd x) ⟩
      Ctx.len Θ ∎

    elts' : {y₀ : Fin (toℕ (xN , x<lenΘ) + 1 + (Ctx.len Θ ∸ suc xN))}
            → {y₁ : Fin (Ctx.len Θ)}
            → PathP (λ i → Fin (lem3 i)) y₀ y₁
            → Ctx.elts (Θ [ sole (Θ [ x ]) / x ]) y₀ ≡ Ctx.elts Θ y₁
    elts' p with toℕ (p i0) ≤? (xN + 1)
    ... | inl z with toℕ (p i0) ≤? xN
    ... | inl x = cong (Ctx.elts Θ) (Σ≡Prop (λ n → isProp≤) λ i → toℕ (p i))
    ... | inr w = cong (Ctx.elts Θ) (Σ≡Prop ((λ n → isProp≤)) lemma)
      where
        lemma' : toℕ (p i0) ≤ xN
        lemma' = pred-≤-pred (1 + toℕ (p i0) ≤≡⟨ z ⟩ +-comm xN 1)
          where open <-Reasoning
        lemma : xN ≡ toℕ (p i1)
        lemma = xN ≡⟨ ≤-antisym w lemma' ⟩ toℕ (p i0) ≡⟨ (λ i → toℕ (p i)) ⟩ toℕ (p i1) ∎

    elts' p | inr z = cong (Ctx.elts Θ) (Σ≡Prop (λ n → isProp≤ ) lem5)
      where
        yN = toℕ (p i0)
        y₁N = toℕ (p i1)
        lem5 : yN ∸ (fst x + 1) + (1 + fst x) ≡ y₁N
        lem5 =
          yN ∸ (fst x + 1) + (1 + fst x) ≡⟨ (λ j → yN ∸ (fst x + 1) + +-comm 1 (fst x) j) ⟩
          yN ∸ (fst x + 1) + (fst x + 1) ≡⟨ ≤-∸-+-cancel z ⟩
          yN ≡⟨ (λ i → toℕ (p i)) ⟩
          y₁N ∎

sole-/L : ∀ {A : Type ℓ} → (a : A) → (Θ : Ctx A) → sole a [ Θ / the-var a ] ≡ Θ
sole-/L a Θ = λ i → record { len = eq-len i ; elts = funExtDep elts' i }
  where
    eq-len : Ctx.len (sole a [ Θ / the-var a ]) ≡ Ctx.len Θ
    eq-len = +-zero (Ctx.len Θ)

    elts' : {y₀ : Fin (Ctx.len (sole a [ Θ / the-var a ]))}{y₁ : Fin (Ctx.len Θ)}
          → PathP (λ i → Fin (eq-len i) ) y₀ y₁
          → Ctx.elts (sole a [ Θ / the-var a ]) y₀ ≡ Ctx.elts Θ y₁
    elts' p with toℕ (p i0) ≤? (0 + Ctx.len Θ)
    ... | inl z with toℕ (p i0) ≤? 0
    ... | inl x = ⊥.rec (¬-<-zero x) -- y₀ < 0, contradiction
    ... | inr z = cong (Ctx.elts Θ) (Σ≡Prop (λ n → isProp≤) λ i → toℕ (p i)) -- y₀ < Ctx.len, done
    elts' p | inr z = ⊥.rec (¬m<m contra) -- y₀ ≡ y₁ and y₀ ≥ len Θ and y₁ < len Θ, contradiction len Θ ≤ y₀ ≡ y₁ < len Θ
      where
        open <-Reasoning
        contra : Ctx.len Θ < Ctx.len Θ
        contra = Ctx.len Θ ≤<⟨ z ⟩
                 (toℕ (p i0) ≡<⟨ (λ i → toℕ (p i)) ⟩
                 (toℕ (p i1) <≡⟨ snd (p i1) ⟩
                 Ctx.len Θ ∎))


nest-var : ∀ {A : Type ℓ} → (Θ₁ Θ₂ : Ctx A) → (x : Var Θ₁) (y : Var Θ₂) →
           Var (Θ₁ [ Θ₂ / x ])
nest-var Θ₁ Θ₂ x y = (toℕ x + toℕ y) , reason
  where
    open <-Reasoning
    reason : toℕ x + toℕ y < toℕ x + Ctx.len Θ₂ + (Ctx.len Θ₁ ∸ suc (fst x))
    reason =
      toℕ x + toℕ y     <≤⟨ <-k+ (snd y) ⟩
      toℕ x + Ctx.len Θ₂ ≤≡⟨ ≤SumLeft ⟩
      toℕ x + Ctx.len Θ₂ + (Ctx.len Θ₁ ∸ suc (fst x)) ∎

postulate nest-/ : ∀ {A : Type ℓ} → (Θ₁ Θ₂ : Ctx A) → (x : Var Θ₁) (y : Var Θ₂)
                 →  Θ₂ [ y ] ≡ Θ₁ [ Θ₂ / x ] [ nest-var Θ₁ Θ₂ x y ]

postulate comp-/-/ : ∀ {A : Type ℓ} → (Θ₁ Θ₂ Θ₃ : Ctx A) → (i : Var Θ₁) (j : Var Θ₂) → Θ₁ [ (Θ₂ [ Θ₃ / j ]) / i ] ≡ Θ₁ [ Θ₂ / i ] [ Θ₃ / nest-var Θ₁ Θ₂ i j ]
