{-# OPTIONS --safe #-}

module Cubical.Categories.Exponentials where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinProduct.More

private
  variable
    ℓC ℓC' : Level

open Category

module _ (C : Category ℓC ℓC') where
  Exponential : (c d : C .ob) → (∀ (e : C .ob) → BinProduct C c e) → Type _
  Exponential c d c×- = RightAdjointAt C C (BinProductWithF _ c×-) d

  module _ (bp : BinProducts C) where
    private
      _×- : (c : C .ob) → Functor C C
      c ×- = BinProductF _ bp ∘F (Constant C C c ,F Id)

    Exponentials : Type _
    Exponentials = ∀ c → RightAdjoint C C (c ×-)
