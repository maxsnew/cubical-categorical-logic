{- Strength for a monad on a cartesian category is a bit simpler than for monoidal categories -}

{-# OPTIONS --safe #-}
module Cubical.Categories.Monad.Strength.Cartesian where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function renaming (_∘_ to _∘f_)
open import Cubical.Categories.Category hiding (isIso)
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Monad.Base
open import Cubical.Categories.Comonad.Base
open import Cubical.Categories.Comonad.Instances.Environment
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.DistributiveLaw.ComonadOverMonad.Base
open import Cubical.Categories.DistributiveLaw.ComonadOverMonad.BiKleisli.Base
open import Cubical.Tactics.FunctorSolver.Reflection
open import Cubical.Tactics.CategorySolver.Reflection

private
  variable
    ℓ ℓ' : Level

module _ {C : Category ℓ ℓ'} (bp : BinProducts C) (T : Monad C) where
  open Notation C bp
  open NatTrans
  StrengthTrans : Type _
  StrengthTrans = NatTrans (×pF ∘F (Id {C = C} ×F T .fst)) (T .fst ∘F ×pF)
  open Category C

  fix-Γ : ∀ Γ → StrengthTrans → NatTrans (Env Γ (bp Γ) .fst ∘F T .fst) ((T .fst) ∘F Env Γ (bp Γ) .fst)
  fix-Γ Γ σ .N-ob x = σ ⟦ Γ , x ⟧
  -- This is the downside of removing the id in ×pF
  fix-Γ Γ σ .N-hom f = cong₂ _⋆_ (sym (×pF-with-agrees Γ)) refl ∙ σ .N-hom _ ∙ cong₂ _⋆_ refl (cong (T .fst ⟪_⟫) (×pF-with-agrees Γ))

  Strength : Type _
  Strength =
    Σ[ σ ∈ StrengthTrans ]
    ∀ Γ → IsDistributiveLaw (Env Γ (bp Γ)) T (fix-Γ Γ σ)
