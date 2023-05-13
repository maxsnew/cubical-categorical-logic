{-
  Show equivalence of definitions from Profunctor.General
-}

{-# OPTIONS --safe #-}
module Cubical.Categories.Profunctor.Equivalence where

open import Cubical.Categories.Profunctor.General



    -- this seemingly needs univalence
    -- Def1=Def2 : ProfRepresentation ≡ PshFunctorRepresentation
    -- Def1=Def2 = hPropExt {!!} {!!} {!!} {!!}

    -- PshFunctorRepresentation≅ProfRepresentation : Iso PshFunctorRepresentation ProfRepresentation
    -- PshFunctorRepresentation≅ProfRepresentation .Iso.fun = PshFunctorRepresentation→ProfRepresentation
    -- PshFunctorRepresentation≅ProfRepresentation .Iso.inv = ProfRepresentation→PshFunctorRepresentation
    -- PshFunctorRepresentation≅ProfRepresentation .Iso.rightInv = {!!}
    -- PshFunctorRepresentation≅ProfRepresentation .Iso.leftInv = {!!}
