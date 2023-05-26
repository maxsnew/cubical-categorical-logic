{-# OPTIONS --safe #-}
module Cubical.Categories.Limits.BinProduct.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Functor
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Presheaf.Representable
private
  variable
    ℓ ℓ' : Level

open Iso
open UnivElt
open isUniversal
open BinProduct
open Category

module _ (C : Category ℓ ℓ') where
  ProdProf : C o-[ ℓ' ]-* (C ×C C)
  ProdProf = HomFunctor (C ×C C) ∘F ((Fst (C ^op) (C ×C C) ,F Fst (C ^op) (C ×C C)) ,F Snd (C ^op) (C ×C C))

  module Notation (bp : BinProducts C) where
    private
      variable
        a b c d : C .ob
        f g : C [ a , b ]
    _×_ : C .ob → C .ob → C .ob
    a × b = bp a b .binProdOb

    π₁ : C [ a × b , a ]
    π₁ {a}{b} = bp a b .binProdPr₁

    π₂ : C [ a × b , b ]
    π₂ {a}{b} = bp a b .binProdPr₂

    _,p_ : C [ c , a ] → C [ c , b ] → C [ c , a × b ]
    f ,p g = bp _ _ . univProp f g .fst .fst

    _×p_ : C [ a , b ] → C [ c , d ] → C [ a × c , b × d ]
    f ×p g = (f ∘⟨ C ⟩ π₁) ,p (g ∘⟨ C ⟩ π₂)

    β₁ : π₁ ∘⟨ C ⟩ (f ,p g) ≡ f
    β₁ {f = f}{g = g} = bp _ _ .univProp f g .fst .snd .fst

    β₂ : π₂ ∘⟨ C ⟩ (f ,p g) ≡ g
    β₂ {f = f}{g = g} = bp _ _ .univProp f g .fst .snd .snd

    -- η : f ≡ (π₁ ∘⟨ C ⟩ f ,p π₂ ∘⟨ C ⟩ f)
    -- η {f = f}= {!!}

  module _ (bp : BinProducts C) where
    open Notation bp
    BinProductsToUnivElts : ParamUnivElt (C ×C C) C ProdProf
    BinProductsToUnivElts (a , b) .vertex = a × b
    BinProductsToUnivElts (a , b) .element = π₁ , π₂
    BinProductsToUnivElts (a , b) .universal .coinduction (f1 , f2) = f1 ,p f2
    BinProductsToUnivElts (a , b) .universal .commutes (f1 , f2) =
      cong₂ _,_ (C .⋆IdR _ ∙ up .fst .snd .fst) ((C .⋆IdR _ ∙ up .fst .snd .snd))
      where up = bp a b .univProp f1 f2
    BinProductsToUnivElts (a , b) .universal .is-uniq (f1 , f2) fp commutes =
      cong fst (sym (up .snd (fp , (sym (C .⋆IdR _) ∙ cong fst commutes) , sym (C .⋆IdR _) ∙ cong snd commutes)))
      where up = bp a b .univProp f1 f2

    BinProductsToProfRepresentation : ProfRepresentation (C ×C C) C ProdProf
    BinProductsToProfRepresentation = PshFunctorRepresentation→ProfRepresentation _ _ _ (ParamUniversalElement→PshFunctorRepresentation _ _ _ (ParamUnivElt→ParamUniversalElement _ _ _ BinProductsToUnivElts))

    BinProductF : Functor (C ×C C) C
    BinProductF = BinProductsToProfRepresentation .fst

  -- todo: make this an iso.
