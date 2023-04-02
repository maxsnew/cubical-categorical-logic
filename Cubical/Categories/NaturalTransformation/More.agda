{-# OPTIONS --safe #-}
module Cubical.Categories.NaturalTransformation.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism renaming (iso to iIso)
open import Cubical.Data.Sigma
open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functor.Properties
open import Cubical.Categories.Commutativity
open import Cubical.Categories.Morphism
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation.Base

private
  variable
    ℓA ℓA' ℓB ℓB' ℓC ℓC' ℓD ℓD' : Level

open Category
open NatTrans
open NatIso
open isIsoC
module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} where
  seqNatIso : {F G H : Functor C D} → NatIso F G → NatIso G H → NatIso F H
  seqNatIso ı ı' .trans = seqTrans (ı .trans) (ı' .trans)
  seqNatIso ı ı' .nIso x .inv = ı' .nIso x .inv ⋆⟨ D ⟩ ı .nIso x .inv
  seqNatIso ı ı' .nIso x .sec =
    D .⋆Assoc _ _ _
    ∙ cong (_⋆_ D (ı' .nIso x .inv))
      (sym (D .⋆Assoc _ _ _)
      ∙ cong (D ∘ ı' .trans .N-ob x) (ı .nIso x .sec)
      ∙ D .⋆IdL (ı' .trans .N-ob x))
    ∙ ı' .nIso x .sec
  seqNatIso ı ı' .nIso x .ret =
    (sym (D .⋆Assoc _ _ _))
    ∙ cong (_∘_ D (ı .nIso x .inv))
      (D .⋆Assoc _ _ _
      ∙ cong (D ⋆ ı .trans .N-ob x) (ı' .nIso x .ret)
      ∙ D .⋆IdR (ı .trans .N-ob x))
    ∙ ı .nIso x .ret
