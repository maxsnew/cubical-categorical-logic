{-# OPTIONS --safe #-}

module Cubical.Categories.Exponentials where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinProduct.More

private
  variable
    ℓC ℓC' : Level

open Category

module _ (C : Category ℓC ℓC')  (bp : BinProducts C) where
  private
    _×- : (c : C .ob) → Functor C C
    c ×- = BinProductF _ bp ∘F (Constant C C c ,F Id)
  Exponential : (c d : C .ob) → Type _
  Exponential c = RightAdjointAt C C (c ×-)

  Exponentials : Type _
  Exponentials = ∀ c d → Exponential c d
