{-
  Show equivalence of definitions from Profunctor.General
-}

{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Profunctor.Equivalence where

open import Cubical.Categories.Profunctor.General
open import Cubical.Foundations.Prelude hiding (Path)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Path
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function renaming (_∘_ to _∘f_)

open import Cubical.Data.Graph.Base
open import Cubical.Data.Graph.Path
open import Cubical.Data.Sigma.Properties

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Functors.HomFunctor

open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Instances.Functors.More
open import Cubical.Categories.Yoneda.More


open import Cubical.Categories.Equivalence.Base
open import Cubical.Categories.Equivalence.Properties
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Cubical.Categories.NaturalTransformation.More

open import Cubical.Categories.Presheaf.Representable
open import Cubical.Tactics.CategorySolver.Reflection


open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Categories.Presheaf.More

private
  variable ℓC ℓC' ℓD ℓD' ℓs : Level

module _ (C : Category ℓC ℓC') (D : Category ℓD ℓD') (R : C *-[ ℓs ]-o D)
  (isUnivC : isUnivalent C ) (isUnivD : isUnivalent D) where

  open isUnivalent

  isUnivProf*-o : (ℓ : Level) → isUnivalent (PROF*-o C D ℓ)
  isUnivProf*-o ℓ = isUnivalentFUNCTOR (D ^op ×C C) (SET ℓ) (isUnivalentSET)

  isPropProfRepresents : (G : Functor C D) → isProp (ProfRepresents C D R G)
  isPropProfRepresents G η η' = 
   NatIso≡ {f = η} {g = η'} (funExt (λ (d , c) → {!refl!}))
       


  -- TODO not exactuly sure how to build this. Can get paths between
  -- (LiftF ∘F Functor→Prof*-o C D) G and
  -- (LiftF ∘F Functor→Prof*-o C D) G'
  -- Can then maybe use properties of LiftF, Functor→Prof*-o and sigma types
  -- to get that x and y are path equal? seems like a stretch
  -- Hope that
  -- 1. We get G ≡ G' from properties of LiftF and Functor→Prof*-o
  -- 2. We get p ≡ p' from isPropProfRepresents
  isPropProfRepresentation : isProp (ProfRepresentation C D R)
  isPropProfRepresentation (G , p) (G' , p') =
    Σ≡Prop (λ F → {!!}) {!!}
  --
  -- sym (
  --   CatIsoToPath (isUnivProf*-o _)
  --   (NatIso→FUNCTORIso (D ^op ×C C) (SET _) (p))
  -- )
  --   ∙
  -- CatIsoToPath (isUnivProf*-o _)
  -- (NatIso→FUNCTORIso (D ^op ×C C) (SET _) (p'))
  

  -- this seemingly needs univalence
  ProfRepresentation≡PshFunctorRepresentation : ProfRepresentation C D R ≡ PshFunctorRepresentation C D R
  ProfRepresentation≡PshFunctorRepresentation = 
    ua ({!   !})
    -- hPropExt 
    --   {!!} 
    --   {!!} 
    --   (ProfRepresentation→PshFunctorRepresentation C D R) 
    --   (PshFunctorRepresentation→ProfRepresentation C D R)

  open Category
  open NatIso
  open NatTrans
  open Functor
  
  Psh→Prof→Psh : {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {R : C *-[ ℓs ]-o D} 
    (Psh : PshFunctorRepresentation C D R) 
      → (ProfRepresentation→PshFunctorRepresentation C D R) 
          ((PshFunctorRepresentation→ProfRepresentation C D R) Psh
          ) ≡ Psh
  Psh→Prof→Psh {C = C} {D = D} {R = R} (G , η) = 
    let (G' , η') = (ProfRepresentation→PshFunctorRepresentation C D R) ((PshFunctorRepresentation→ProfRepresentation C D R) (G , η)) in
    let G≡G' = Functor≡ (λ _ → refl) (λ _ → refl) in
        ΣPathP (G≡G' ,
          makeNatIsoPathP refl (cong′ (λ X → (Prof*-o→Functor C D) (LiftF ∘F (Functor→Prof*-o C D X))) G≡G')
          (λ i → λ (c : C .ob) → ((
            pathToIso-Square
            {x = (Prof*-o→Functor C D (LiftF ∘F R)) .F-ob c }
            {y = Prof*-o→Functor C D (funcComp LiftF R) .F-ob c }
            {z = Prof*-o→Functor C D (funcComp LiftF (Functor→Prof*-o C D G)) .F-ob c }
            {w = Prof*-o→Functor C D
                   (funcComp LiftF
                    (Functor→Prof*-o C D
                     G'))
                   .F-ob c }
            refl
            (cong′ (λ X → ((Prof*-o→Functor C D) (LiftF {ℓD'}{ℓs} ∘F (Functor→Prof*-o C D X))) .F-ob c ) G≡G')
            (η .trans .N-ob c) (η' .trans .N-ob c) ?) i))
        )

      

  PshFunctorRepresentation≅ProfRepresentation : Iso (PshFunctorRepresentation C D R) (ProfRepresentation C D R)
  PshFunctorRepresentation≅ProfRepresentation .Iso.fun = PshFunctorRepresentation→ProfRepresentation C D R
  PshFunctorRepresentation≅ProfRepresentation .Iso.inv = ProfRepresentation→PshFunctorRepresentation C D R
  PshFunctorRepresentation≅ProfRepresentation .Iso.rightInv = {!   !}
  -- TODO if I try this it hangs
    -- (λ f →
      -- {!
        -- PshFunctorRepresentation→ProfRepresentation C D R (ProfRepresentation→PshFunctorRepresentation C D R f)
        -- ≡⟨ ? ⟩
        -- f ∎
      -- !})
  PshFunctorRepresentation≅ProfRepresentation .Iso.leftInv = {!!}
