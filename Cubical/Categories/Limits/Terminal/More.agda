{-# OPTIONS --safe #-}
module Cubical.Categories.Limits.Terminal.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Limits.Terminal

private
  variable
    ℓ ℓ' ℓc ℓc' ℓd ℓd' : Level

isoToTerminal : ∀ (C : Category ℓ ℓ') (x : Terminal C) y → CatIso C (terminalOb C x) y → isTerminal C y
isoToTerminal C x y x≅y y' .fst = x≅y .fst ∘⟨ C ⟩ terminalArrow C x y'
isoToTerminal C x y x≅y y' .snd f =
  sym (⋆InvRMove (invIso x≅y) (sym (terminalArrowUnique C {T = x} (invIso x≅y .fst ∘⟨ C ⟩ f))))

preservesTerminal : ∀ (C : Category ℓc ℓc')(D : Category ℓd ℓd')
                  → Functor C D
                  → Type (ℓ-max (ℓ-max (ℓ-max ℓc ℓc') ℓd) ℓd')
preservesTerminal C D F = ∀ (One : Terminal C) → isTerminal D (F ⟅ One .fst ⟆)


preserveOnePreservesAll : ∀ (C : Category ℓc ℓc')(D : Category ℓd ℓd')
                        → (F : Functor C D)
                        → (One : Terminal C) → isTerminal D (F ⟅ One .fst ⟆)
                        → preservesTerminal C D F
preserveOnePreservesAll C D F One D-preserves-One One' =
  isoToTerminal D
                ((F ⟅ One .fst ⟆) , D-preserves-One) (F ⟅ One' .fst ⟆)
                (F-Iso {F = F} (terminalToIso C One One'))
