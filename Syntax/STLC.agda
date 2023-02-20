module Syntax.STLC where

open import Cubical.Data.Fin hiding (_/_)
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Nat

private
  variable ℓ ℓ' ℓty ℓtm : Level

open import Context
open Ctx

data Connectives : Type ℓ-zero where

Sig₀ : (ℓ : Level) → Type (ℓ-suc ℓ)
Sig₀ ℓ = hGroupoid ℓ

Ty : (Σ₀ : Sig₀ ℓ) → Type ℓ
Ty Σ₀ = Σ₀ .fst

base-ty : ∀ {Σ₀ : Sig₀ ℓ} → Σ₀ .fst → Ty Σ₀
base-ty A = A

module _ {ℓ} where
  open Ctx

  record Sig₁ (Σ₀ : Sig₀ ℓ) : Type (ℓ-suc ℓ) where
    field
      fun-symbol : Type ℓ
      src : fun-symbol → Ctx (Ty Σ₀)
      tgt : fun-symbol → Ty Σ₀
      isSetFunSymbol : isSet (fun-symbol)
  open Sig₁
  data Tm {Σ₀} (Σ₁ : Sig₁ Σ₀) (Γ : Ctx (Ty Σ₀)) : (A : Ty Σ₀) → Type ℓ where
    var : (x : Var Γ) → Tm Σ₁ Γ (Γ [ x ])
    fun-app : (f : Σ₁ .fun-symbol)
            → substitution (Tm Σ₁ Γ) (Σ₁ .src f)
            → Tm Σ₁ Γ (Σ₁ .tgt f)
  STT-subst : ∀ {Σ₀} → Sig₁ Σ₀ → Ctx (Ty Σ₀) → Ctx (Ty Σ₀) → Type ℓ
  STT-subst Σ₁ Δ Γ = substitution (Tm Σ₁ Δ) Γ

  module isSetTTProof (Σ₀)(Σ₁ : Sig₁ Σ₀) (Γ : Ctx (Ty Σ₀)) where
    open import Cubical.Foundations.HLevels
    open import Cubical.Data.W.Indexed
    open import Cubical.Data.Sum
    open import Cubical.Data.Unit

    Tm-X = Ty Σ₀
    Tm-S : Tm-X → Type ℓ
    Tm-S A = (fiber (Γ [_]) A) ⊎ (fiber (Σ₁ .tgt) A)
    Tm-P : ∀ A → Tm-S A → Type
    Tm-P A (inl x) = ⊥
    Tm-P A (inr f) = Var (Σ₁ .src (f .fst))

    Tm-inX : ∀ A (s : Tm-S A) → Tm-P A s → Ty Σ₀
    Tm-inX A (inr f) p = Σ₁ .src (f .fst) [ p ]

    Tm→W : ∀ {A} → Tm Σ₁ Γ A → IW Tm-S Tm-P Tm-inX A
    Tm→W (var x) = node (inl (x , refl)) λ ()
    Tm→W (fun-app f γ) = node (inr (f , refl)) (λ x → Tm→W (γ x))

    W→Tm : ∀ {A} → IW Tm-S Tm-P Tm-inX A → Tm Σ₁ Γ A
    W→Tm (node (inl (x , ty≡A)) subtree) = transport (cong (Tm Σ₁ Γ) ty≡A) (var x)
    W→Tm (node (inr (f , ty≡A)) subtree) = transport (cong (Tm Σ₁ Γ) ty≡A) (fun-app f (λ x → W→Tm (subtree x)))

    TmRetractofW : ∀ {A} (M : Tm Σ₁ Γ A) → W→Tm (Tm→W M) ≡ M
    TmRetractofW (var x)       = transportRefl (var x)
    TmRetractofW (fun-app f γ) = transportRefl (fun-app f (λ x → W→Tm (Tm→W (γ x)))) ∙ cong (fun-app f) (funExt (λ x → TmRetractofW (γ x)))

    isSetTm-S : ∀ A → isSet (Tm-S A)
    isSetTm-S A = isSet⊎ (isSetΣ isSetFin λ x → Σ₀ .snd (Γ [ x ]) A) (isSetΣ (Σ₁ .isSetFunSymbol) (λ x → Σ₀ .snd (Σ₁ .tgt x) A))

    isSetTm : ∀ A → isSet (Tm Σ₁ Γ A)
    isSetTm A = isSetRetract Tm→W W→Tm TmRetractofW (isOfHLevelSuc-IW 1 isSetTm-S A)

    isSetSubst : ∀ Δ → isSet (STT-subst Σ₁ Γ Δ)
    isSetSubst Δ = isSetΠ λ x → isSetTm (Δ [ x ])

  _⟨_⟩ : ∀ {Σ₀}{Σ₁ : Sig₁ Σ₀}{Δ Γ : Ctx (Ty Σ₀)}{A : Ty Σ₀}
       → Tm Σ₁ Γ A → STT-subst Σ₁ Δ Γ
       → Tm Σ₁ Δ A
  var x ⟨ γ ⟩ = γ x
  fun-app f δ ⟨ ξ ⟩ = fun-app f (λ x → δ x ⟨ ξ ⟩)

  id-subst : ∀ {Σ₀}{Σ₁ : Sig₁ Σ₀} → (Γ : Ctx (Ty Σ₀)) → STT-subst Σ₁ Γ Γ
  id-subst Γ x = var x

  comp-subst : ∀ {Σ₀}{Σ₁ : Sig₁ Σ₀} → {Ξ Δ Γ : Ctx (Ty Σ₀)}
             → STT-subst Σ₁ Δ Γ → STT-subst Σ₁ Ξ Δ
             → STT-subst Σ₁ Ξ Γ
  comp-subst γ δ x = γ x ⟨ δ ⟩

  subst-idInp : ∀ {Σ₀}{Σ₁ : Sig₁ Σ₀}{Γ}{A}
              → (M : Tm Σ₁ Γ A)
              → M ⟨ id-subst Γ ⟩ ≡ M
  subst-idInp {Γ = Γ}{A = A} (var x) = refl
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
