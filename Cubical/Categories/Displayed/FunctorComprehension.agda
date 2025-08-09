{-# OPTIONS --safe --lossy-unification #-}
{--
 -- Displayed Functor Comprehension
 -- Construction of a Displayed Functor by defining displayed universal elements
 --}
module Cubical.Categories.Displayed.FunctorComprehension where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.FunctorComprehension
open import Cubical.Categories.Yoneda

import Cubical.Categories.Constructions.TotalCategory as TotalCat

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Profunctor
open import Cubical.Categories.Displayed.Presheaf
import Cubical.Categories.Displayed.Reasoning as Reasoning

private
  variable
    ℓC ℓC' ℓD ℓD' ℓS : Level
    ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' ℓSᴰ : Level

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
         {P : Profunctor C D ℓS}
         {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
         (Pᴰ : Profunctorᴰ P Cᴰ Dᴰ ℓSᴰ)
         {ues : UniversalElements P}
         (uesᴰ : UniversalElementsᴰ ues Pᴰ)
       where
  private
    ∫FunctorComprehension : Functor (TotalCat.∫C Cᴰ) (TotalCat.∫C Dᴰ)
    ∫FunctorComprehension =
      FunctorComprehension (∫Prof Pᴰ) (∫ues Pᴰ uesᴰ)
    module Dᴰ = Reasoning Dᴰ

  open Functor
  open Functorᴰ
  FunctorᴰComprehension : Functorᴰ (FunctorComprehension P ues) Cᴰ Dᴰ
  FunctorᴰComprehension .F-obᴰ xᴰ = (∫FunctorComprehension ⟅ _ , xᴰ ⟆) .snd
  FunctorᴰComprehension .F-homᴰ fᴰ = (∫FunctorComprehension ⟪ _ , fᴰ ⟫) .snd
  FunctorᴰComprehension .Functorᴰ.F-idᴰ =
    Dᴰ.rectify $ Dᴰ.≡out (∫FunctorComprehension .F-id)
  FunctorᴰComprehension .Functorᴰ.F-seqᴰ fᴰ gᴰ =
    Dᴰ.rectify $ Dᴰ.≡out $ ∫FunctorComprehension .F-seq (_ , fᴰ) (_ , gᴰ)

module _ {C : Category ℓC ℓC'}
         {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ C ℓDᴰ ℓDᴰ'}
         {Pᴰ : Profunctorⱽ Cᴰ Dᴰ ℓSᴰ}
         (uesⱽ : UniversalElementsⱽ Pᴰ) where

  private
    module Cᴰ = Categoryᴰ Cᴰ
    module Dᴰ = Categoryᴰ Dᴰ

    F : Functor C C
    F = FunctorComprehension YO (selfUnivElt C)

    F≡ : F ≡ Id
    F≡ = Functor≡ (λ _ → refl) (Category.⋆IdL C)

    Fᴰ : Functorᴰ (FunctorComprehension YO (selfUnivElt C)) Cᴰ Dᴰ
    Fᴰ = FunctorᴰComprehension Pᴰ λ x xᴰ → UniversalElementⱽ.toUniversalᴰ (uesⱽ x xᴰ)

  -- WARNING: reindF
  -- The reind is only needed on morphisms. Would probably be
  -- preferable to have a reindF'' that is Eq on objects but path on
  -- morphisms
  FunctorⱽComprehension : Functorⱽ Cᴰ Dᴰ
  FunctorⱽComprehension = reindF F≡ Fᴰ

  FunctorⱽComprehension-ob-filler :
    ∀ {c} (cᴰ : Cᴰ.ob[ c ]) →
    PathP (λ i → Dᴰ.ob[ F≡ i .Functor.F-ob c ])
      (Fᴰ .Functorᴰ.F-obᴰ cᴰ)
      (FunctorⱽComprehension .Functorᴰ.F-obᴰ cᴰ)
  FunctorⱽComprehension-ob-filler = reindF-ob-filler F≡ Fᴰ
