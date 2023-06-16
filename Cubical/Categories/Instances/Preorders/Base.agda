{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.Preorders.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Relation.Binary.Preorder

open import Cubical.Categories.Instances.Preorders.Monotone

private
  variable
    ℓ ℓ' : Level

open Category

-- Category of Posets
PREORDER : (ℓ ℓ' : Level) → Category _ _
PREORDER ℓ ℓ' = record
  { ob = Preorder ℓ ℓ'
  ; Hom[_,_] = λ X Y → MonFun X Y
  ; id = MonId
  ; _⋆_ = MonComp
  ; ⋆IdL = λ {X} {Y} f → eqMon f f refl
  ; ⋆IdR = λ {X} {Y} f → eqMon f f refl
  ; ⋆Assoc = λ {X} {Y} {Z} {W} f g h → eqMon _ _ refl
  ; isSetHom = MonFunIsSet
  }
