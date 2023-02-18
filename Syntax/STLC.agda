module Syntax.STLC where

open import Cubical.Data.Fin hiding (_/_)
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Foundations.Prelude

open import Context

private
  variable ℓ ℓ' ℓty ℓtm : Level

data Connectives : Type ℓ-zero where

Sig₀ : (ℓ : Level) → Type (ℓ-suc ℓ)
Sig₀ ℓ = Type ℓ

data Ty (Σ₀ : Sig₀ ℓ) : Type ℓ where
  base-ty : Σ₀ → Ty Σ₀

module _ {ℓ} where
  open Ctx

  record Sig₁ (Σ₀ : Sig₀ ℓ) : Type (ℓ-suc ℓ) where
    field
      fun-symbol : Type ℓ
      src : fun-symbol → Ctx (Ty Σ₀)
      tgt : fun-symbol → Ty Σ₀
      isSetFunSymbol : isSet fun-symbol
  open Sig₁
  data Tm {Σ₀} (Σ₁ : Sig₁ Σ₀) (Γ : Ctx (Ty Σ₀)) : Ty Σ₀ → Type ℓ where
    var : (x : Var Γ) → Tm Σ₁ Γ (Γ [ x ])
    fun-app : (f : Σ₁ .fun-symbol)
            → substitution (Tm Σ₁ Γ) (Σ₁ .src f)
            → Tm Σ₁ Γ (Σ₁ .tgt f)
  STT-subst : ∀ {Σ₀} → Sig₁ Σ₀ → Ctx (Ty Σ₀) → Ctx (Ty Σ₀) → Type ℓ
  STT-subst Σ₁ Δ Γ = substitution (Tm Σ₁ Δ) Γ

  -- module isSetTTProof (Σ₀)(Σ₁ : Sig₁ Σ₀) where
  --   STTCode : ∀ {Γ}{Al Ar} → Tm Σ₁ Γ Al → Tm Σ₁ Γ Ar → Type ℓ
  --   STTCode (var x) (var y) = Lift (x ≡ y)
  --   STTCode (var x) (fun-app f x₁) = Lift ⊥
  --   STTCode (fun-app f x) (var x₁) = Lift ⊥
  --   STTCode {Γ} (fun-app f γ) (fun-app g δ) = Σ[ p ∈ f ≡ g ] PathP (λ i → STT-subst Σ₁ Γ (Σ₁ .src (p i))) {!!} {!!}

  -- isSetSTTTerm : ∀ {Σ₀}{Σ₁ : Sig₁ Σ₀}{Γ}{A} → isSet (Tm Σ₁ Γ A)
  -- isSetSTTTerm = {!!}
  
  _⟨_⟩ : ∀ {Σ₀}{Σ₁ : Sig₁ Σ₀}{Δ Γ : Ctx (Ty Σ₀)}{A : Ty Σ₀}
       → Tm Σ₁ Γ A → STT-subst Σ₁ Δ Γ
       → Tm Σ₁ Δ A
  var x ⟨ γ ⟩ = γ x
  fun-app f δ ⟨ ξ ⟩ = fun-app f (λ x → δ x ⟨ ξ ⟩)

  id-subst : ∀ {Σ₀}{Σ₁ : Sig₁ Σ₀} → (Γ : Ctx (Ty Σ₀)) → STT-subst Σ₁ Γ Γ
  id-subst _ = var

  comp-subst : ∀ {Σ₀}{Σ₁ : Sig₁ Σ₀} → {Ξ Δ Γ : Ctx (Ty Σ₀)}
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
