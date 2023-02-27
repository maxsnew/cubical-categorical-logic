module Syntax.STLC.Semantics.Interpretation where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf

open import Syntax.STLC hiding (Tm) renaming (Ty to SimpleTy)
open import NaturalModels.Cartesian
open import NamedContext
open import UMP

private
  variable
    ℓ ℓ' ℓb ℓb' ℓt ℓt' : Level

open CartesianCategory
open Category
open SimplyTypedCategory
open UnivElt
open Ctx
open Sig₁ 

Interp₀ : Sig₀ ℓ → SimplyTypedCategory ℓb ℓb' ℓt ℓt' → Type _
Interp₀ Σ₀ C = Σ₀ .fst → C .Ty

interpTy : ∀ {Σ₀ : Sig₀ ℓ}{S : SimplyTypedCategory ℓb ℓb' ℓt ℓt'} → Interp₀ Σ₀ S → SimpleTy Σ₀ → S .Ty
interpTy i = i

interpCtx : ∀ {Σ₀ : Sig₀ ℓ}{S : SimplyTypedCategory ℓb ℓb' ℓt ℓt'} → Interp₀ Σ₀ S → Ctx (SimpleTy Σ₀) → S .B .cat .ob
interpCtx {S = S} i Γ =
  S .B .finite-products
       ((Γ .var) , (Γ .isFinSetVar))
       (λ x → S .Tm-repr (i (Γ .el x)) .vertex) .vertex

Interp₁ : ∀ {Σ₀ : Sig₀ ℓ}{S : SimplyTypedCategory ℓb ℓb' ℓt ℓt'} → Interp₀ Σ₀ S → Sig₁ Σ₀ ℓ' → Type _
Interp₁ {Σ₀ = Σ₀}{S = S} i Σ₁ =
  ∀ (f : Σ₁ .fun-symbol)
  → ((S .Tm (i (Σ₁ .tgt f))) ⟅ interpCtx {Σ₀ = Σ₀}{S = S} i (Σ₁ .src f) ⟆) .fst
