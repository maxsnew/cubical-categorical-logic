-- Grothendieck Construction for a Displayed Category
{-# OPTIONS --safe #-}
module Cubical.Categories.Constructions.DisplayedCategory.Grothendieck where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor

open import Cubical.Categories.Constructions.DisplayedCategory
open import Cubical.Categories.Constructions.DisplayedCategory.DisplayedPoset

private
  variable
    ℓC ℓC' ℓP : Level

module _ {ℓC ℓC' : Level} {ℓP : Level} (C : Category ℓC ℓC') where

  open Category

  -- the Grothendieck construction, or the generalized construction
  -- for a subcategory
  Grothendieck : DisplayedCategory {_} {_} {ℓP} C → Category _ _
  Grothendieck D = record
    { ob =  Σ[ x ∈ C .ob ] D-ob x
    ; Hom[_,_] = λ (x , Dx) (y , Dy) →
                 Σ[ f ∈ C [ x , y ] ] D-Hom f [ Dx , Dy ]
    ; id = (C .id) , D-id
    ; _⋆_ = λ (f , Df) (g , Dg) → (f ⋆⟨ C ⟩ g) , (Df D-⋆ Dg)
    ; ⋆IdL = λ (f , Df) → ΣPathP ( C .⋆IdL f , D-⋆IdL Df )
    ; ⋆IdR = λ (f , Df) → ΣPathP ( C .⋆IdR f , D-⋆IdR Df )
    ; ⋆Assoc = λ (f , Df) (g , Dg) (h , Dh)
             → ΣPathP ( C .⋆Assoc f g h , D-⋆Assoc Df Dg Dh )
    ; isSetHom =  isSetΣ (C .isSetHom) (λ _ → isSetHomf)
    } where
      open DisplayedCategory D

  open Functor

  GrothendieckForgetful : {D : DisplayedCategory {_} {_} {ℓP} C} →
                          Functor (Grothendieck D) C
  GrothendieckForgetful .F-ob = fst
  GrothendieckForgetful .F-hom = fst
  GrothendieckForgetful .F-id = refl
  GrothendieckForgetful {D} .F-seq =
    λ f g → cong {x = f ⋆⟨ Grothendieck D ⟩ g} fst refl

  open DisplayedPoset

  GrothendieckForgetfulIsFaithful : (D : DisplayedPoset {_} {_} {ℓP} C) →
                                    isFaithful
                                    (GrothendieckForgetful
                                      {DisplayedPoset→Cat C D})
  GrothendieckForgetfulIsFaithful D x y f g p =
    ΣPathP (p , isProp→PathP (λ i → D .isPropHomf {f = p i}) (f .snd) (g .snd))

