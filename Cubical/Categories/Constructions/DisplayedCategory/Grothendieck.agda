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

  -- The Grothendieck construction, or the generalized construction
  -- for a subcategory
  Grothendieck : DisplayedCategory C ℓP → Category _ _
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

  -- The first projection from the Grothendieck construction to the original
  -- category
  Fst : {D : DisplayedCategory {_} {_} {ℓP} C} →
                          Functor (Grothendieck D) C
  Fst .F-ob = fst
  Fst .F-hom = fst
  Fst .F-id = refl
  Fst {D} .F-seq =
    λ f g → cong {x = f ⋆⟨ Grothendieck D ⟩ g} fst refl

  open DisplayedPoset

  -- The first projection is faithful in the case of a displayed poset
  isFaithfulFst : (D : DisplayedPoset {_} {_} {ℓP} C) →
                                    isFaithful
                                    (Fst {DisplayedPoset→Cat C D})
  isFaithfulFst D x y f g p =
    ΣPathP (p , isProp→PathP (λ i → D .isPropHomf {f = p i}) (f .snd) (g .snd))

