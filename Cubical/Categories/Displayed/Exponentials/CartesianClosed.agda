{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Displayed.Exponentials.CartesianClosed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Exponentials

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Constructions.Slice
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Exponentials.Base
open import Cubical.Categories.Displayed.Fibration
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Limits.Cartesian
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Quantifiers

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open CartesianClosedCategory
open CartesianCategoryᴰ
open CartesianCategory
record CartesianClosedCategoryᴰ (CCC : CartesianClosedCategory ℓC ℓC') (ℓCᴰ ℓCᴰ' : Level) : Type _ where
  no-eta-equality
  field
    CCᴰ : CartesianCategoryᴰ (CCC .CC) ℓCᴰ ℓCᴰ'
    expᴰ : Exponentialsᴰ
      (CCᴰ .Cᴰ)
      (CCC .CC .bp)
      (AllExponentiable→Exponentials (CCC .CC .C) (CCC .CC .bp) (CCC .exps))
      (CCᴰ .bpᴰ)

open CartesianCategoryⱽ
CartesianClosedCategoryⱽ :
  Category ℓC ℓC' → (ℓCᴰ ℓCᴰ' : Level) → Type _
CartesianClosedCategoryⱽ C ℓCᴰ ℓCᴰ' =
  Σ[ CCⱽ ∈ CartesianCategoryⱽ C ℓCᴰ ℓCᴰ' ]
  Σ[ bp ∈ BinProducts C ]
  Exponentialsⱽ (Cᴰ CCⱽ) (bpⱽ CCⱽ) (cartesianLifts CCⱽ)
  × UniversalQuantifiers bp (isFibration→isFibration' $ CCⱽ .cartesianLifts)
