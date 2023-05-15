{-# OPTIONS --safe #-}

module Cubical.Categories.Functors.More where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functors.Constant

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

open Category
open Functor

ConstantComposeFunctor :
  (C : Category ℓC ℓC') (D : Category ℓD ℓD' ) (c : C .ob)
  (F : Functor C D) → Constant (D ^op) D (F .F-ob c) ≡ F ∘F Constant (D ^op) C c
ConstantComposeFunctor C D c F = Functor≡
  (λ c → ( refl ))
    (λ f → (
      D .id
     ≡⟨ sym (F .F-id) ⟩
       F ⟪ Constant (D ^op) C c ⟪ f ⟫ ⟫ ∎
  ))
