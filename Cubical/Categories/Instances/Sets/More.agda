{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.Sets.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.BinProduct

private
  variable
    ℓ ℓ' : Level

open Functor
-- Lift functor
LiftF : Functor (SET ℓ) (SET (ℓ-max ℓ ℓ'))
LiftF {ℓ}{ℓ'} .F-ob A = (Lift {ℓ}{ℓ'} (A .fst)) , isOfHLevelLift 2 (A .snd)
LiftF .F-hom f x = lift (f (x .lower))
LiftF .F-id = refl
LiftF .F-seq f g = funExt λ x → refl

×Sets : Functor (SET ℓ ×C SET ℓ) (SET ℓ)
×Sets .F-ob (A , B) = ⟨ A ⟩ × ⟨ B ⟩ , isSet× (A .snd) (B .snd)
×Sets .F-hom (f , g) (x , y) = (f x) , (g y)
×Sets .F-id = refl
×Sets .F-seq f g = refl
