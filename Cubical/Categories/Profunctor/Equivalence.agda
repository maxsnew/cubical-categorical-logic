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

module _ (C : Category ℓC ℓC') (D : Category ℓD ℓD') (R : C *-[ ℓs ]-o D) where

  open Category
  open NatIso
  open NatTrans
  open Functor

  PshFunctorRepresentation≅ProfRepresentation : Iso (PshFunctorRepresentation C D R) (ProfRepresentation C D R)
  PshFunctorRepresentation≅ProfRepresentation =
    record {
      fun = PshFunctorRepresentation→ProfRepresentation C D R;
      inv = ProfRepresentation→PshFunctorRepresentation C D R;
      rightInv = Prof→Psh→Prof;
      leftInv = Psh→Prof→Psh
    }
    where
    Prof→Psh→Prof : (Prof : ProfRepresentation C D R)
        → (PshFunctorRepresentation→ProfRepresentation C D R)
          ((ProfRepresentation→PshFunctorRepresentation C D R) Prof
          ) ≡ Prof
    Prof→Psh→Prof (G , η) =
      let (G' , η') = (PshFunctorRepresentation→ProfRepresentation C D R) ((ProfRepresentation→PshFunctorRepresentation C D R) (G , η)) in
      let G≡G' = Functor≡ (λ _ → refl) (λ _ → refl) in
        ΣPathP (G≡G' ,
          makeNatIsoPathP
            refl
            (cong′ (λ X → (LiftF ∘F (Functor→Prof*-o C D X))) G≡G')
            (funExt λ (d , c) →
              funExt λ _ → refl
            )
        )
    Psh→Prof→Psh : (Psh : PshFunctorRepresentation C D R)
      → (ProfRepresentation→PshFunctorRepresentation C D R)
        ((PshFunctorRepresentation→ProfRepresentation C D R) Psh
        ) ≡ Psh
    Psh→Prof→Psh (G , η) =
      let (G' , η') = (ProfRepresentation→PshFunctorRepresentation C D R) ((PshFunctorRepresentation→ProfRepresentation C D R) (G , η)) in
      let G≡G' = Functor≡ (λ _ → refl) (λ _ → refl) in
          ΣPathP (G≡G' ,
            makeNatIsoPathP refl (cong′ (λ X → (Prof*-o→Functor C D) (LiftF ∘F (Functor→Prof*-o C D X))) G≡G')
            (funExt (λ (c : C .ob) →
              makeNatTransPathP
                refl
                (cong′ (λ X → (Prof*-o→Functor C D (LiftF {ℓD'}{ℓs} ∘F (Functor→Prof*-o C D X))) .F-ob c) G≡G')
                (funExt (λ (d : D .ob) →
                  funExt λ _ → refl
                ))
              ))
          )
