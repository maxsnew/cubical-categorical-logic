{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.Functors.More where

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
open import Cubical.Categories.Constructions.BinProduct

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

module _ (C : Category ℓC ℓC') (D : Category ℓD ℓD') where
  open Category
  open Functor
  open NatTrans

  appF : Functor ((FUNCTOR C D) ×C C) D
  appF .F-ob (F , c) = F ⟅ c ⟆
  appF .F-hom {x = (F , c)}{y = (F' , c')} (α , f) = F ⟪ f ⟫ ⋆⟨ D ⟩ α .N-ob c'
  appF .F-id {x = (F , c)}=
    F ⟪ C .id ⟫ ⋆⟨ D ⟩ D .id ≡[ i ]⟨ F .F-id i ⋆⟨ D ⟩ D .id ⟩
    D .id ⋆⟨ D ⟩ D .id ≡⟨ D .⋆IdR (D .id) ⟩
    D .id ∎
  appF .F-seq {x = (F , c)}{y = (F' , c')}{z = (F'' , c'')}(α , f) (α' , f') =
    -- Functor solver would be useful here...
    F ⟪ f ⋆⟨ C ⟩ f' ⟫ ⋆⟨ D ⟩ (α .N-ob _ ⋆⟨ D ⟩ α' .N-ob c'')
      ≡[ i ]⟨ F .F-seq f f' i ⋆⟨ D ⟩ (α .N-ob _ ⋆⟨ D ⟩ α' .N-ob c'') ⟩
    (F ⟪ f ⟫ ⋆⟨ D ⟩ F ⟪ f' ⟫) ⋆⟨ D ⟩ (α .N-ob _ ⋆⟨ D ⟩ α' .N-ob c'')
      ≡⟨ D .⋆Assoc (F ⟪ f ⟫) (F ⟪ f' ⟫) ((α .N-ob _ ⋆⟨ D ⟩ α' .N-ob c'')) ⟩
    F ⟪ f ⟫ ⋆⟨ D ⟩ (F ⟪ f' ⟫ ⋆⟨ D ⟩ (α .N-ob _ ⋆⟨ D ⟩ α' .N-ob c''))
      ≡[ i ]⟨ F ⟪ f ⟫ ⋆⟨ D ⟩ D .⋆Assoc (F ⟪ f' ⟫) (α .N-ob _) (α' .N-ob c'') (~ i) ⟩
    F ⟪ f ⟫ ⋆⟨ D ⟩ ((F ⟪ f' ⟫ ⋆⟨ D ⟩ α .N-ob _) ⋆⟨ D ⟩ α' .N-ob c'')
      ≡[ i ]⟨ F ⟪ f ⟫ ⋆⟨ D ⟩ (α .N-hom f' i ⋆⟨ D ⟩ α' .N-ob c'') ⟩
    F ⟪ f ⟫ ⋆⟨ D ⟩ ((α .N-ob _ ⋆⟨ D ⟩ F' ⟪ f' ⟫) ⋆⟨ D ⟩ α' .N-ob c'')
      ≡[ i ]⟨ F ⟪ f ⟫ ⋆⟨ D ⟩ D .⋆Assoc (α .N-ob _) (F' ⟪ f' ⟫) (α' .N-ob c'') i ⟩
    F ⟪ f ⟫ ⋆⟨ D ⟩ (α .N-ob _ ⋆⟨ D ⟩ (F' ⟪ f' ⟫ ⋆⟨ D ⟩ α' .N-ob c''))
      ≡[ i ]⟨ D .⋆Assoc (F ⟪ f ⟫) (α .N-ob _) ((F' ⟪ f' ⟫ ⋆⟨ D ⟩ α' .N-ob c'')) (~ i) ⟩
    (F ⟪ f ⟫ ⋆⟨ D ⟩ α .N-ob c') ⋆⟨ D ⟩ (F' ⟪ f' ⟫ ⋆⟨ D ⟩ α' .N-ob c'') ∎
