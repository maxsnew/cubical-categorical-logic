{-# OPTIONS --safe #-}

module Cubical.Categories.Constructions.DisplayedCategory where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category

private
  variable
    ℓC ℓC' ℓP : Level

module _ {ℓC ℓC' : Level} {ℓP : Level} (C : Category ℓC ℓC') where

  open Category


  record DisplayedCategory : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-suc ℓP)) where
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
