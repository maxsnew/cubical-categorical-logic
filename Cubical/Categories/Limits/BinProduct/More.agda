{-# OPTIONS --safe #-}
module Cubical.Categories.Limits.BinProduct.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.BinProduct.More
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Functor
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Adjoint.UniversalElements
private
  variable
    ℓ ℓ' : Level

open Iso
open UnivElt
open isUniversal
open BinProduct
open Category

module _ (C : Category ℓ ℓ') where
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

  BinProductToRepresentable : ∀ {a b} → BinProduct C a b → RightAdjointAt _ _ (Δ C) (a , b)
  BinProductToRepresentable bp .vertex = bp .binProdOb
  BinProductToRepresentable bp .element = (bp .binProdPr₁) , (bp .binProdPr₂)
  BinProductToRepresentable bp .universal .coinduction (f1 , f2) = bp .univProp f1 f2 .fst .fst
  BinProductToRepresentable bp .universal .commutes (f1 , f2) = cong₂ _,_ (C .⋆IdR _ ∙ up .fst .snd .fst) ((C .⋆IdR _ ∙ up .fst .snd .snd))
    where up = bp .univProp f1 f2
  BinProductToRepresentable bp .universal .is-uniq (f1 , f2) fp commutes = cong fst (sym (bp .univProp f1 f2 .snd (fp , (sym (C .⋆IdR _) ∙ cong fst commutes) , sym (C .⋆IdR _) ∙ cong snd commutes)))

  module _ {a} (bp : ∀ b → BinProduct C a b) where
    ProdAProf : C o-[ ℓ' ]-* C
    ProdAProf = HomFunctor (C ×C C) ∘F ((Δ C ^opF) ×F (Constant C C a ,F Id))

    -- There should be a less repetive way to do this...
    BinProductWithToRepresentable : ParamUnivElt C C ProdAProf
    BinProductWithToRepresentable b .vertex = bp b .binProdOb
    BinProductWithToRepresentable b .element .fst = bp b .binProdPr₁
    BinProductWithToRepresentable b .element .snd = bp b .binProdPr₂
    BinProductWithToRepresentable b .universal .coinduction (f1 , f2) = bp b .univProp f1 f2 .fst .fst
    BinProductWithToRepresentable b .universal .commutes (f1 , f2) = cong₂ _,_ (C .⋆IdR _ ∙ up .fst .snd .fst) ((C .⋆IdR _ ∙ up .fst .snd .snd))
      where up = bp b .univProp f1 f2
    BinProductWithToRepresentable b .universal .is-uniq (f1 , f2) fp commutes = cong fst (sym (bp b .univProp f1 f2 .snd (fp , (sym (C .⋆IdR _) ∙ cong fst commutes) , sym (C .⋆IdR _) ∙ cong snd commutes)))

    -- Univ
    BinProductWithF : Functor C C
    BinProductWithF = pr .fst
      where pr : ProfRepresentation C C ProdAProf
            pr = ParamUnivElt→ProfRepresentation _ _ _ BinProductWithToRepresentable

  module _ (bp : BinProducts C) where
    BinProductsToUnivElts : RightAdjoint C (C ×C C) (Δ C)
    BinProductsToUnivElts c = BinProductToRepresentable (bp (c .fst) (c .snd))

    ProdProf : C o-[ ℓ' ]-* (C ×C C)
    ProdProf = Functor→Profo-* C (C ×C C) (Δ C)

    BinProductsToProfRepresentation : ProfRepresentation (C ×C C) C ProdProf
    BinProductsToProfRepresentation = ParamUnivElt→ProfRepresentation _ _ _ BinProductsToUnivElts

    BinProductF : Functor (C ×C C) C
    BinProductF = BinProductsToProfRepresentation .fst

  -- -- -- todo: make this an iso.
