{-# OPTIONS --safe #-}
module Cubical.Categories.Comonad.Instances.Environment where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function renaming (_∘_ to _∘f_)
open import Cubical.Categories.Category hiding (isIso)
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Monad.Base
open import Cubical.Categories.Comonad.Base
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinProduct.More

open import Cubical.Categories.DistributiveLaw.ComonadOverMonad.Base
open import Cubical.Tactics.FunctorSolver.Reflection
private
  variable
    ℓ ℓ' : Level

module _ {C : Category ℓ ℓ'} (Γ : Category.ob C) (Γ×- : ∀ c → BinProduct C Γ c) where
  open Category C
  open IsComonad
  open BinProduct
  open NatTrans
  Γ×-F : Functor C C
  Γ×-F = BinProductWithF C Γ×-

  Γ×-F-Como : IsComonad Γ×-F
  -- This should follow from some abstract nonsense
  Γ×-F-Como .ε .N-ob x = Γ×- x .binProdPr₂
  Γ×-F-Como .ε .N-hom {x}{y} f = Γ×- y .univProp _ _ .fst .snd .snd
  Γ×-F-Como .δ .N-ob x = Γ×- (Γ×- x .binProdOb) .univProp (Γ×- x .binProdPr₁) id .fst .fst
  Γ×-F-Como .δ .N-hom {x}{y} f = {!!}
  Γ×-F-Como .idl-δ = {!!}
  Γ×-F-Como .idr-δ = {!!}
  Γ×-F-Como .assoc-δ = {!!}

  Env : Comonad C
  Env = Γ×-F , Γ×-F-Como

module _ {C : Category ℓ ℓ'} (bp : BinProducts C) where
  open Category C
  Env' : ob → Comonad C
  Env' Γ = Env Γ (bp Γ)

  pull : {Δ Γ : ob} (γ : Hom[ Δ , Γ ]) → ComonadHom (Env Γ (bp Γ)) (Env Δ (bp Δ))
  pull = {!!}

  pull-id : ∀ {Γ} → pull (id {Γ}) .fst ≡ idTrans (Env' Γ .fst)
  pull-id = {!!}

  pull-comp : ∀ {Θ Δ Γ} (γ : Hom[ Δ , Γ ])(δ : Hom[ Θ , Δ ])
          → pull (γ ∘ δ) .fst ≡ pull δ .fst ∘ᵛ pull γ .fst
  pull-comp = {!!}
