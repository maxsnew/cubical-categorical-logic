{-
  Show equivalence of definitions from Profunctor.General
-}

{-# OPTIONS --safe #-}
-- module Cubical.Categories.Profunctor.Equivalence where
module Cubical.Categories.Profunctor.Equiv where

open import Cubical.Categories.Profunctor.General

open import Cubical.Foundations.Prelude hiding (Path)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Path
open import Cubical.Foundations.Function renaming (_∘_ to _∘f_)
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Graph.Base
open import Cubical.Data.Graph.Path
open import Cubical.Data.Sigma.Properties

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Bifunctor.Base
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.Elements
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Limits.Terminal

open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Instances.Functors.More
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Presheaf.More

open import Cubical.Tactics.CategorySolver.Reflection
open import Cubical.Tactics.FunctorSolver.Reflection




private
  variable ℓC ℓC' ℓD ℓD' ℓS : Level

module _ (C : Category ℓC ℓC') (D : Category ℓD ℓD') (R : C *-[ ℓS ]-o D) where

  open Category
  open NatIso
  open NatTrans
  open Functor
  open Contravariant

  ProfRepresentation≅PshFunctorRepresentation : Iso (ProfRepresentation C D R) (PshFunctorRepresentation C D R)
  ProfRepresentation≅PshFunctorRepresentation =
    record {
     fun = (ProfRepresentation→PshFunctorRepresentation C D R) ;
     inv = (PshFunctorRepresentation→ProfRepresentation C D R) ;
     rightInv = Psh→Prof→Psh ;
     leftInv = Prof→Psh→Prof
    }
    where
    Psh→Prof→Psh : (Psh : PshFunctorRepresentation C D R)
      → (ProfRepresentation→PshFunctorRepresentation C D R)
        ((PshFunctorRepresentation→ProfRepresentation C D R) Psh)
        ≡ Psh
    Psh→Prof→Psh (G , η) =
      ΣPathP (
        refl ,
        makeNatIsoPathP
          refl
          refl
          (funExt (λ c → makeNatTransPath (funExt (λ d → refl))))
      )

    Prof→Psh→Prof : (Prof : ProfRepresentation C D R)
      → (PshFunctorRepresentation→ProfRepresentation C D R)
        ((ProfRepresentation→PshFunctorRepresentation C D R) Prof)
        ≡ Prof
    Prof→Psh→Prof (G , η) =
      ΣPathP (
        refl ,
        ΣPathP (
        -- TODO to show this we need to prove that two ProfHomos are path
        -- equal, but I don't think we have a nonrefl way to do this
        -- (and its not a refl)
          {!!} ,
          {!!}
        )
      )

  -- TODO port over Equiv23.agda
  -- 2 sleepy to do rn
  PshFunctorRepresentation≅ParamUnivElt : Iso (PshFunctorRepresentation C D R) (ParamUnivElt C D R)
  PshFunctorRepresentation≅ParamUnivElt =
    record {
      fun = (PshFunctorRepresentation→ParamUnivElt C D R) ;
      inv = (ParamUnivElt→PshFunctorRepresentation C D R) ;
      rightInv = {!!} ;
      leftInv = {!!}
    }


  ParamUnivElt≅ParamUniversalElement : Iso (ParamUnivElt C D R) (ParamUniversalElement C D R)
  ParamUnivElt≅ParamUniversalElement =
    iso
      (ParamUnivElt→ParamUniversalElement C D R)
      (ParamUniversalElement→ParamUnivElt C D R)
      (λ U → funExt λ c → Σ≡Prop (isPropIsTerminal (∫ᴾ_ {C = D} (pAppR R c))) refl)
      λ U → refl

  ProfRepresentation≅ParamUnivElt : Iso (ProfRepresentation C D R) (ParamUnivElt C D R)
  ProfRepresentation≅ParamUnivElt = compIso ProfRepresentation≅PshFunctorRepresentation PshFunctorRepresentation≅ParamUnivElt

  ProfRepresentation≅ParamUniversalElement : Iso (ProfRepresentation C D R) (ParamUniversalElement C D R)
  ProfRepresentation≅ParamUniversalElement = compIso ProfRepresentation≅ParamUnivElt ParamUnivElt≅ParamUniversalElement

  PshFunctorRepresentation≅ParamUniversalElement : Iso (PshFunctorRepresentation C D R) (ParamUniversalElement C D R)
  PshFunctorRepresentation≅ParamUniversalElement = compIso PshFunctorRepresentation≅ParamUnivElt ParamUnivElt≅ParamUniversalElement
