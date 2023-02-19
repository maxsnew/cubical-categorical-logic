module Syntax.STLC where

open import Cubical.Data.Fin hiding (_/_)
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Nat

private
  variable ℓ ℓ' ℓty ℓtm : Level

open import Context
open Ctx

data Connectives : Type ℓ-zero where

Sig₀ : (ℓ : Level) → Type (ℓ-suc ℓ)
Sig₀ ℓ = Type ℓ

data Ty (Σ₀ : Sig₀ ℓ) : Type ℓ where
  base-ty : Σ₀ → Ty Σ₀

module _ {ℓ} where
  open Ctx

  record Sig₁ (Σ₀ : Sig₀ ℓ) : Type (ℓ-suc ℓ) where
    field
      fun-symbol : ∀ (A : Ty Σ₀) → Type ℓ
      src : ∀ {A} → fun-symbol A → ICtx (Ty Σ₀)
      isSetFunSymbol : ∀ {A} → isSet (fun-symbol A)
  open Sig₁
  data Tm {Σ₀} (Σ₁ : Sig₁ Σ₀) (Γ : ICtx (Ty Σ₀)) (A : Ty Σ₀) : Type ℓ where
    var : IVar Γ A → Tm Σ₁ Γ A
    fun-app : (f : Σ₁ .fun-symbol A)
            → isubstitution (Tm Σ₁ Γ) (Σ₁ .src f)
            → Tm Σ₁ Γ A
  STT-subst : ∀ {Σ₀} → Sig₁ Σ₀ → ICtx (Ty Σ₀) → ICtx (Ty Σ₀) → Type ℓ
  STT-subst Σ₁ Δ Γ = isubstitution (Tm Σ₁ Δ) Γ

  module isSetTTProof (Σ₀)(Σ₁ : Sig₁ Σ₀) (Γ : ICtx (Ty Σ₀)) where
    open import Cubical.Foundations.HLevels
    open import Cubical.Data.W.Indexed
    open import Cubical.Data.Sum
    open import Cubical.Data.Unit

    Tm-X = Ty Σ₀
    Tm-S : Tm-X → Type ℓ
    Tm-S A = IVar Γ A ⊎ Σ₁ .fun-symbol A
    Tm-P : ∀ A → Tm-S A → Type ℓ
    Tm-P A (inl x) = Lift ⊥
    Tm-P A (inr f) = AnyIVar (Σ₁ .src f)

    Tm-inX : ∀ A (s : Tm-S A) → Tm-P A s → Ty Σ₀
    Tm-inX A (inr f) p = p .fst

    Tm→W : ∀ {A} → Tm Σ₁ Γ A → IW Tm-S Tm-P Tm-inX A
    Tm→W (var x) = node (inl x) (λ p → ⊥.rec (lower p))
    Tm→W (fun-app f γ) = node (inr f) (λ p → Tm→W (γ p))

    W→Tm : ∀ {A} → IW Tm-S Tm-P Tm-inX A → Tm Σ₁ Γ A
    W→Tm (node (inl x) subtree) = var x
    W→Tm (node (inr f) subtree) = fun-app f λ x → W→Tm (subtree x)

    TmRetractofW : ∀ {A} (M : Tm Σ₁ Γ A) → W→Tm (Tm→W M) ≡ M
    TmRetractofW (var x) = refl
    TmRetractofW (fun-app f γ) = cong (fun-app f) λ i x → TmRetractofW (γ x) i

    isSetTm-S : ∀ A → isSet (Tm-S A)
    isSetTm-S A = isSet⊎ isSetFin (Σ₁ .isSetFunSymbol)

    isSetTm : ∀ A → isSet (Tm Σ₁ Γ A)
    isSetTm A = isSetRetract Tm→W W→Tm TmRetractofW (isOfHLevelSuc-IW 1 isSetTm-S A)

    isSetSubst : ∀ Δ → isSet (STT-subst Σ₁ Γ Δ)
    isSetSubst Δ = isSetΠ λ x → isSetTm (x .fst)

  _⟨_⟩ : ∀ {Σ₀}{Σ₁ : Sig₁ Σ₀}{Δ Γ : ICtx (Ty Σ₀)}{A : Ty Σ₀}
       → Tm Σ₁ Γ A → STT-subst Σ₁ Δ Γ
       → Tm Σ₁ Δ A
  var x ⟨ γ ⟩ = γ (_ , x)
  fun-app f δ ⟨ ξ ⟩ = fun-app f (λ x → δ x ⟨ ξ ⟩)

  id-subst : ∀ {Σ₀}{Σ₁ : Sig₁ Σ₀} → (Γ : ICtx (Ty Σ₀)) → STT-subst Σ₁ Γ Γ
  id-subst Γ x = var (x .snd)

  comp-subst : ∀ {Σ₀}{Σ₁ : Sig₁ Σ₀} → {Ξ Δ Γ : ICtx (Ty Σ₀)}
             → STT-subst Σ₁ Δ Γ → STT-subst Σ₁ Ξ Δ
             → STT-subst Σ₁ Ξ Γ
  comp-subst γ δ x = γ x ⟨ δ ⟩

  subst-idInp : ∀ {Σ₀}{Σ₁ : Sig₁ Σ₀}{Γ}{A}
              → (M : Tm Σ₁ Γ A)
              → M ⟨ id-subst Γ ⟩ ≡ M
  subst-idInp (var x) = refl
  subst-idInp (fun-app f γ) = λ i → fun-app f (λ x → subst-idInp (γ x) i)

  subst-Assoc : ∀ {Σ₀}{Σ₁ : Sig₁ Σ₀}{Ξ}{Δ}{Γ}{A}
              → (M : Tm Σ₁ Γ A)
              → (γ : STT-subst Σ₁ Δ Γ)
              → (δ : STT-subst Σ₁ Ξ Δ)
              → M ⟨ comp-subst γ δ ⟩ ≡ M ⟨ γ ⟩ ⟨ δ ⟩
  subst-Assoc (var x) γ δ = refl
  subst-Assoc (fun-app f γ) δ ξ = λ i → fun-app f (funExt (λ x i → subst-Assoc (γ x) δ ξ i) i)

  comp-subst-IdInp : ∀ {Σ₀}{Σ₁ : Sig₁ Σ₀}{Δ Γ}
                   → (γ : STT-subst Σ₁ Δ Γ)
                   → comp-subst γ (id-subst Δ) ≡ γ
  comp-subst-IdInp γ = λ i x → subst-idInp (γ x) i

  comp-subst-IdOutp : ∀ {Σ₀}{Σ₁ : Sig₁ Σ₀}{Δ Γ}
                    → (γ : STT-subst Σ₁ Δ Γ)
                    → comp-subst (id-subst Γ) γ ≡ γ
  comp-subst-IdOutp γ = refl

  comp-subst-Assoc : ∀ {Σ₀}{Σ₁ : Sig₁ Σ₀}{Ψ Ξ Δ Γ}
                   → (γ : STT-subst Σ₁ Δ Γ)
                   → (δ : STT-subst Σ₁ Ξ Δ)
                   → (ξ : STT-subst Σ₁ Ψ Ξ)
                   → comp-subst γ (comp-subst δ ξ) ≡ comp-subst (comp-subst γ δ) ξ
  comp-subst-Assoc γ δ ξ = funExt (λ x i → subst-Assoc (γ x) δ ξ i)
