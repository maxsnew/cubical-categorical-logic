{-# OPTIONS --safe #-}

module Cubical.Categories.Constructions.DisplayedCategory where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category

private
  variable
    ℓC ℓC' ℓP : Level

module _ {ℓC ℓC' : Level} (C : Category ℓC ℓC') where

  open Category

  record DisplayedCategory (ℓP : Level) : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-suc ℓP)) where
    field
      D-ob : C .ob → Type ℓP
      D-Hom_[_,_] : {a b : C .ob} → (f : C [ a , b ])
                  → (x : D-ob a) → (y : D-ob b) → Type ℓP
      isSetHomf : {a b : C .ob} → {f : C [ a , b ]}
                  → {x : D-ob a} → {y : D-ob b} → isSet (D-Hom f [ x , y ])
      D-id : {a : C .ob} → {x : D-ob a} → D-Hom (C .id) [ x , x ]
      _D-⋆_ : {a b c : C .ob} → {f : C [ a , b ]} → {g : C [ b , c ]}
            → {x : D-ob a} → {y : D-ob b} → {z : D-ob c}
            → (k : D-Hom f [ x , y ]) → (l : D-Hom g [ y , z ])
            → D-Hom (f ⋆⟨ C ⟩ g) [ x , z ]
      D-⋆IdL : {a b : C .ob} → {f : C [ a , b ]}
            → {x : D-ob a} → {y : D-ob b}
            → (k : D-Hom f [ x , y ])
            → PathP (λ i → D-Hom (C .⋆IdL f i) [ x , y ]) (D-id D-⋆ k) k
      D-⋆IdR : {a b : C .ob} → {f : C [ a , b ]}
            → {x : D-ob a} → {y : D-ob b}
            → (k : D-Hom f [ x , y ])
            → PathP (λ i → D-Hom (C .⋆IdR f i) [ x , y ]) (k D-⋆ D-id) k
      D-⋆Assoc : {a b c d : C .ob}
                   → {f : C [ a , b ]} → {g : C [ b , c ]} → {h : C [ c , d ]}
                   → {x : D-ob a} → {y : D-ob b} → {z : D-ob c} → {w : D-ob d}
                   → (k : D-Hom f [ x , y ])
                   → (l : D-Hom g [ y , z ])
                   → (m : D-Hom h [ z , w ])
                   → PathP (λ i → D-Hom (C .⋆Assoc f g h i) [ x , w ])
                     ((k D-⋆ l) D-⋆ m)
                     (k D-⋆ (l D-⋆ m))

open Category
open DisplayedCategory
-- Helpful syntax/notation
D-hom' : {C : Category ℓC ℓC'}(D : DisplayedCategory C ℓP) → {c c' : C .ob}
        → (d : D .D-ob c)
        → (d' : D .D-ob c')
        → (f : C [ c , c' ])
        → Type ℓP
D-hom' D d d' f = D-Hom_[_,_] D f d d'

-- TODO: idea for a better notation PLEASE
syntax D-hom' D d d' f = D ⊨ f d[ d , d' ]

module _ {C : Category ℓC ℓC'} (D : DisplayedCategory C ℓP) where
  open DisplayedCategory
  record Section : Type (ℓ-max (ℓ-max ℓC ℓC') ℓP) where
    field
      S-ob  : ∀ c → D .D-ob c
      S-hom : ∀ {c c'} → (f : C [ c , c' ]) (d : D .D-ob c)(d' : D .D-ob c')
            → D ⊨ f d[ d , d' ]
      S-id  : ∀ {c} d → S-hom (C .id {c}) d d ≡ D .D-id
      S-seq : ∀ {c c' c''} {d d' d''}
              (f : C [ c , c' ])(f' : C [ c' , c'' ])
            → S-hom (f ⋆⟨ C ⟩ f') d d'' ≡ D ._D-⋆_ (S-hom f d d') (S-hom f' d' d'')
