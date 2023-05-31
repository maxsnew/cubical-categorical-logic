{-# OPTIONS --safe #-}
module Cubical.Categories.Comonad.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor renaming (𝟙⟨_⟩ to funcId)
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.NaturalTransformation.Properties
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Constructions.BinProduct

private
  variable
    ℓ ℓ' : Level

module _ {C : Category ℓ ℓ'} (W : Functor C C) where
  open Category C
  open Functor
  open NatTrans

  record IsComonad : Type (ℓ-max ℓ ℓ') where
    field
      ε : NatTrans W (funcId C)
      δ : NatTrans W (funcComp W W)
      idl-δ : PathP (λ i → NatTrans W (F-rUnit {F = W} i)) ((ε ∘ˡ W) ∘ᵛ δ) (idTrans W)
      idr-δ : PathP (λ i → NatTrans W (F-lUnit {F = W} i)) ((W ∘ʳ ε) ∘ᵛ δ) (idTrans W)
      assoc-δ : PathP (λ i → NatTrans W (F-assoc {F = W} {G = W} {H = W} i))
                      ((W ∘ʳ δ) ∘ᵛ δ)
                      ((δ ∘ˡ W) ∘ᵛ δ)

module _ (C : Category ℓ ℓ') where
  Comonad : Type (ℓ-max ℓ ℓ')
  Comonad = Σ[ D ∈ Functor C C ] IsComonad D

