{-# OPTIONS --safe #-}
module Cubical.Categories.Profunctor.AsBifunctor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function renaming (_∘_ to _∘f_)

open import Cubical.Categories.Category hiding (isIso)
open import Cubical.Categories.Functor
open import Cubical.Categories.Bifunctor.Base
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Functors.More
open import Cubical.Categories.Functors.HomFunctor

open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Instances.Functors.More

private
  variable
    ℓC ℓC' ℓD ℓD' ℓS ℓR : Level

_o-[_]-*_ : (C : Category ℓC ℓC') → ∀ ℓS → (D : Category ℓD ℓD') → Type _
C o-[ ℓS ]-* D = Bifunctor (C ^op) D (SET ℓS)

_*-[_]-o_ : (C : Category ℓC ℓC') → ∀ ℓS → (D : Category ℓD ℓD') → Type _
C *-[ ℓS ]-o D = D o-[ ℓS ]-* C

module _  {C : Category ℓC ℓC'}{D : Category ℓD ℓD'} (R : C o-[ ℓR ]-* D) (S : C o-[ ℓS ]-* D) where
  -- A definition of profunctor homomorphism that avoids Lifts

  ℓmaxCDSR : Level
  ℓmaxCDSR = (ℓ-max ℓC (ℓ-max ℓC' (ℓ-max ℓD (ℓ-max ℓD' (ℓ-max ℓS ℓR)))))

  open NatIso
  open Functor

  record ProfHomo : Type ℓmaxCDSR where
    field
      PH-ob : ∀ {c d} → (r : ⟨ R ⟅ c , d ⟆b ⟩) → ⟨ S ⟅ c , d ⟆b ⟩
      PH-natL : ∀ {c c' d} (f : C [ c , c' ]) (r : ⟨ R ⟅ c' , d ⟆b ⟩)
              → PH-ob ((R ⟪ f ⟫l) r) ≡ (S ⟪ f ⟫l) (PH-ob r)
      PH-natR : ∀ {c d d'} (r : ⟨ R ⟅ c , d ⟆b ⟩) (g : D [ d , d' ])
              → PH-ob ((R ⟪ g ⟫r) r) ≡ (S ⟪ g ⟫r) (PH-ob r)

    nat-iso-out-of-product : NatIso (LiftF {ℓR}{ℓmaxCDSR} ∘F (Bifunctor→Functor R)) (LiftF {ℓS}{ℓmaxCDSR} ∘F Bifunctor→Functor S)
    nat-iso-out-of-product .trans =
      natTrans
      (λ x x₁ → lift (PH-ob (lower x₁)))
      (λ {(c , d)} {(c' , d')}  f →
          funExt (λ x → 
            ((λ x₂ → lift (PH-ob (lower x₂)))
              ∘f
            (funcComp LiftF (Bifunctor→Functor R) .F-hom f))
              x
              ≡⟨ (({!λ i → lift ((PH-natR (lower x) (f .snd)) i)!})) ⟩
            {!!}
              ≡⟨ (({!PH-natR (lower x) (f .snd)!})) ⟩
            ((funcComp LiftF (Bifunctor→Functor S) .F-hom f)
              ∘f
            (λ x₂ → lift (PH-ob (lower x₂))))
              x
            ∎
         )
      )
    nat-iso-out-of-product .nIso = {!!}

  open ProfHomo
  ProfIso : Type _
  ProfIso = Σ[ ϕ ∈ ProfHomo ] ∀ c d → isIso (ϕ .PH-ob {c}{d})

open ProfHomo

Functor→Prof*-o : (C : Category ℓC ℓC') (D : Category ℓD ℓD') (F : Functor C D) → C *-[ ℓD' ]-o D
Functor→Prof*-o C D F = HomBif D ∘Fr F

Functor→Profo-* : (C : Category ℓC ℓC') (D : Category ℓD ℓD') (F : Functor C D) → C o-[ ℓD' ]-* D
Functor→Profo-* C D F = HomBif D ∘Fl (F ^opF)

Prof*-o→Functor : (C : Category ℓC ℓC') (D : Category ℓD ℓD') (R : C *-[ ℓS ]-o D) → Functor C (FUNCTOR (D ^op) (SET ℓS))
Prof*-o→Functor C D R = curryFl (D ^op) (SET _) ⟅ Bifunctor→Functor R ⟆

Profo-*→Functor : (C : Category ℓC ℓC') (D : Category ℓD ℓD') (R : C o-[ ℓS ]-* D) → Functor (C ^op) (FUNCTOR D (SET ℓS))
Profo-*→Functor C D R = curryF D (SET _) ⟅ Bifunctor→Functor R ⟆

module _ (C : Category ℓC ℓC') (D : Category ℓD ℓD') (R : C *-[ ℓS ]-o D) where
  open Category
  open Functor
  open UnivElt
  open isUniversal
  open Bifunctor

  ProfRepresents : Functor C D → Type _
  ProfRepresents G = ProfIso {C = D}{D = C} R (Functor→Prof*-o C D G)

  ProfRepresentation : Type _
  ProfRepresentation = Σ[ G ∈ Functor C D ] ProfRepresents G

  PshFunctorRepresentation : Type _
  PshFunctorRepresentation =
    Σ[ G ∈ Functor C D ]
    NatIso (Prof*-o→Functor C D ((LiftF {ℓS}{ℓD'}) ∘Fp R ))
           (Prof*-o→Functor C D (LiftF {ℓD'}{ℓS} ∘Fp (Functor→Prof*-o C D G)))


  RepresentableAt : (c : C .ob) → Type _
  RepresentableAt c = UnivElt D (pAppR R c)

  ParamUnivElt : Type _
  ParamUnivElt = (c : C .ob) → RepresentableAt c

  ParamUniversalElement : Type _
  ParamUniversalElement = (c : C .ob) → UniversalElement D (pAppR R c)

  ProfRepresentation→PshFunctorRepresentation : ProfRepresentation → PshFunctorRepresentation
  ProfRepresentation→PshFunctorRepresentation (G , η) =
    G , preservesNatIsosF (curryFl (D ^op) (SET _)) {!η!}
    -- (G ,
    -- (preservesNatIsosF (curryFl (D ^op) (SET _)) η)
    -- )


  ParamUnivElt→Functor : ParamUnivElt → Functor C D
  ParamUnivElt→Functor ues .F-ob c = ues c .vertex
  ParamUnivElt→Functor ues .F-hom {x = c}{y = c'} f = ues c' .universal .coinduction ((R ⟪ f ⟫r) (ues c .element))
  ParamUnivElt→Functor ues .F-id {x = c} =
    cong (ues c .universal .coinduction) (λ i → R .Bif-idR i (ues c .element))
    ∙ sym (coinduction-elt (ues c .universal))
  ParamUnivElt→Functor ues .F-seq {x = c}{y = c'}{z = c''} f g =
    -- Both sides are ≡ to R .Bif-homR (ues c .vertex) g (R .Bif-homR (ues c .vertex) f (ues c .element))
    cong (ues c'' .universal .coinduction) ((λ i → R .Bif-seqR f g i (ues c .element)))
    ∙ cong (coinduction (ues c'' .universal))
        ( cong (R .Bif-homR (ues c .vertex) g)
          (sym (ues c' .universal .commutes _))
        ∙ (λ i → R .Bif-assoc (ues c' .universal .coinduction ((R ⟪ f ⟫r) (ues c .element))) g i (ues c' .element)))
    ∙ sym (coinduction-natural (ues c'' .universal) _ _)
