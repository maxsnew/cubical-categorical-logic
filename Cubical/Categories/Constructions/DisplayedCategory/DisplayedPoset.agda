{-# OPTIONS --safe #-}
module Cubical.Categories.Constructions.DisplayedCategory.DisplayedPoset where
-- Special Case of Displayed Category where morphisms have a Prop
-- rather than a set. Useful in constructing subcategories

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Categories.Category

open import Cubical.Categories.Constructions.DisplayedCategory

private
  variable
    ℓC ℓC' ℓP : Level

module _ {ℓC ℓC' : Level} {ℓP : Level} (C : Category ℓC ℓC') where

  open Category

  {-
    When the morphism set is a prop,
    the Id/Assoc/isSet properties are all degenerate.
    This record passed to the Grothendieck construction
    will pick out a subset of objects (D-ob) and morphisms (D-hom)
  -}
  record DisplayedPoset : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-suc ℓP)) where
    field
      D-ob : C .ob → Type ℓP
      D-Hom_[_,_] : {a b : C .ob} → (f : C [ a , b ])
                  → (x : D-ob a) → (y : D-ob b) → Type ℓP
      isPropHomf :{a b : C .ob} → {f : C [ a , b ]}
                  → {x : D-ob a} → {y : D-ob b} → isProp (D-Hom f [ x , y ])
      D-id : {a : C .ob} → {x : D-ob a} → D-Hom (C .id) [ x , x ]
      _D-⋆_ : {a b c : C .ob} → {f : C [ a , b ]} → {g : C [ b , c ]}
            → {x : D-ob a} → {y : D-ob b} → {z : D-ob c}
            → (k : D-Hom f [ x , y ]) → (l : D-Hom g [ y , z ])
            → D-Hom (f ⋆⟨ C ⟩ g) [ x , z ]

  DisplayedPoset→Cat : (D : DisplayedPoset) → (DisplayedCategory C ℓP)
  DisplayedPoset→Cat D = record
    { D-ob = D-ob
    ; D-Hom_[_,_] = D-Hom_[_,_]
    ; isSetHomf = isProp→isSet (isPropHomf)
    ; D-id = D-id
    ; _D-⋆_ = _D-⋆_
    ; D-⋆IdL = λ k →
        isProp→PathP (λ i → isPropHomf {f = ((C .⋆IdL _) i)}) _ _
    ; D-⋆IdR = λ k →
        isProp→PathP (λ i → isPropHomf {f = ((C .⋆IdR _) i)}) _ _
    ; D-⋆Assoc = λ k l m →
        isProp→PathP (λ i → isPropHomf {f = ((C .⋆Assoc _ _ _) i)}) _ _
    } where
    open DisplayedPoset D
