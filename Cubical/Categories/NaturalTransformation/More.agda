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
    ℓA ℓA' ℓB ℓB' ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level

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

  CAT⋆IdR : {F : Functor C D} → NatIso (Id ∘F F) F
  CAT⋆IdR {F} .trans .N-ob = idTrans F .N-ob
  CAT⋆IdR {F} .trans .N-hom = idTrans F .N-hom
  CAT⋆IdR {F} .nIso = idNatIso F .nIso

module _ {B : Category ℓB ℓB'}{C : Category ℓC ℓC'}{D : Category ℓD ℓD'} where
  _∘ʳi_ : ∀ (K : Functor C D) → {G H : Functor B C} (β : NatIso G H)
       → NatIso (K ∘F G) (K ∘F H)
  _∘ʳi_ K β .trans = K ∘ʳ β .trans
  _∘ʳi_ K β .nIso x = preserveIsosF {F = K} (β .trans .N-ob _ , β .nIso x) .snd


  CAT⋆Assoc : {E : Category ℓE ℓE'}
            (F : Functor B C)(G : Functor C D)(H : Functor D E)
            → NatIso (H ∘F (G ∘F F)) ((H ∘F G) ∘F F)
  CAT⋆Assoc F G H .trans .N-ob = idTrans ((H ∘F G) ∘F F) .N-ob
  CAT⋆Assoc F G H .trans .N-hom = idTrans ((H ∘F G) ∘F F) .N-hom
  CAT⋆Assoc F G H .nIso = idNatIso ((H ∘F G) ∘F F) .nIso
