{-# OPTIONS --safe #-}

module Cubical.Categories.Equivalence.More where

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.NaturalTransformation.Properties
open import Cubical.Categories.Morphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Functor.Properties
open import Cubical.Categories.Equivalence.Base
open import Cubical.Categories.Category

open import Cubical.Tactics.CategorySolver.Reflection

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' ℓ ℓ' : Level


module _ 
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {E : Category ℓE ℓE'} 
  (F : Functor C D) (G : Functor D E)
  where
  
  open Category
  open Functor
  open NatTrans
  open isEquivalence
  open NatIso

  isEquivalenceComp : isEquivalence F → isEquivalence G → isEquivalence (G ∘F F)
  isEquivalenceComp Feq Geq = record { invFunc = F'G' ; η = η-iso ; ε = ε-iso } where
    F'G' : Functor E C
    F'G' = Feq .invFunc ∘F  Geq .invFunc
    η-iso : NatIso 𝟙⟨ C ⟩ (F'G' ∘F (G ∘F F))
    η-iso .trans .N-ob c = Feq .invFunc .F-hom (Geq .η .trans .N-ob (F .F-ob c))
    η-iso .trans .N-hom = {!   !}
    η-iso .nIso = {!   !}
    ε-iso : NatIso ((G ∘F F) ∘F F'G') 𝟙⟨ E ⟩
    ε-iso = {!   !}