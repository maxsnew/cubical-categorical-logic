{-# OPTIONS --safe #-}

-- The Category of Elements

open import Cubical.Categories.Category

module Cubical.Categories.Constructions.Elements.More where

open import Cubical.Categories.Instances.Sets
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Categories.Functor
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Categories.Constructions.Elements

import Cubical.Categories.Morphism as Morphism
import Cubical.Categories.Constructions.Slice as Slice

open Category
open Functor

-- module _ {ℓ ℓ'} {C : Category ℓ ℓ'} {ℓS} (F : Functor C (SET ℓS)) where
--   -- An isomorphism in the category of elements is equivalent to
--   -- an isomorphism in the original category paired with 
--   module _ ⦃ isU : isUnivalent C ⦄ where
--     open Covariant {C = C}
--     open isUnivalent
--     -- open Iso
--     -- open isIsoC
--     module _ { xf yg : (∫ F) .ob } where
--       private
--         x = xf .fst
--         y = yg .fst
--       pathIsoEquiv : (x ≡ y) ≃ (CatIso _ x y)
--       pathIsoEquiv = univEquiv isU x y

--       isoPathEquiv : (CatIso _ x y) ≃ (x ≡ y)
--       isoPathEquiv = invEquiv pathIsoEquiv

--       pToIIso' : Iso (x ≡ y) (CatIso _ x y)
--       pToIIso' = equivToIso pathIsoEquiv
--     instance
--       preservesUnivalence∫ : isUnivalent (∫ F)
--       preservesUnivalence∫ .univ x y = isoToIsEquiv {!!} where
--         sIso : Iso (x ≡ y) (CatIso (∫ F) x y)
--         sIso .Iso.fun p = pathToIso p
--         sIso .Iso.inv = {!!}
--         sIso .Iso.rightInv = {!!}
--         sIso .Iso.leftInv = {!!}
      

module _ {ℓ ℓ'} {C : Category ℓ ℓ'} {ℓS} (F : Functor (C ^op) (SET ℓS)) where
  open Contravariant {C = C}
  Elementᴾ : Type (ℓ-max ℓ ℓS)
  Elementᴾ = (∫ᴾ F) .ob
  
  ∫ᴾhomEqSimpl : ∀ {o1 o2} (f g : (∫ᴾ F) [ o1 , o2 ])
               → fst f ≡ fst g → f ≡ g
  ∫ᴾhomEqSimpl f g p = ∫ᴾhomEq {F = F} f g refl refl p
    
