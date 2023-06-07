-- TODO: Better Name?
-- The cartesian product of categories, but presented by the universal property
-- that is is left adjoint to forming functor categories
--
-- C ×C D → E ≅ C → FUNCTOR D E
{-# OPTIONS --safe #-}

module Cubical.Categories.Constructions.BinProduct.AsLeftAdjoint where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base hiding (Id)
open import Cubical.Categories.NaturalTransformation hiding (_⟦_⟧)
open import Cubical.Data.Graph.Base
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Sigma

open import Cubical.Categories.Constructions.Free.Category as Free
open import Cubical.Categories.Constructions.Presented as Presented
open import Cubical.Categories.Bifunctor hiding (Bifunctor→Functor; UniversalBifunctor)

private
  variable
    ℓc ℓc' ℓd ℓd' : Level

open Category
open Functor
open Quiver
open Interp
open Axioms


module _ (C : Category ℓc ℓc') (D : Category ℓd ℓd') where
  data ProdGenerator : Type (ℓ-max (ℓ-max ℓc ℓc') (ℓ-max ℓd ℓd')) where
    _id×_ : ∀ (c : C .ob) {d d' : D .ob} (g : D [ d , d' ]) → ProdGenerator
    _×id_ : ∀ {c c' : C .ob} (f : C [ c , c' ]) (d : D .ob) → ProdGenerator
    _×ₑ_ : ∀ {c c' : C .ob}{d d' : D .ob} (f : C [ c , c' ]) (g : D [ d , d' ]) → ProdGenerator

  data ProdAx : Type (ℓ-max (ℓ-max ℓc ℓc') (ℓ-max ℓd ℓd')) where
    combine-id×id : ∀ {c c' d d'} (f : C [ c , c' ])(g : D [ d , d' ])
                → ProdAx
    combine-×id× : ∀ {c c' d d'} (f : C [ c , c' ])(g : D [ d , d' ])
                → ProdAx
    id×-Id   : ∀ (c : C .ob) (d : D .ob) → ProdAx
    id×-Comp : ∀ (c : C .ob) {d d' d'' : D .ob}
               (g' : D [ d' , d'' ])(g : D [ d , d' ])
             → ProdAx
    ×id-Id   : ∀ (c : C .ob) (d : D .ob) → ProdAx
    ×id-Comp : ∀ {c c' c'' : C .ob}
               (f' : C [ c' , c'' ])(f : C [ c , c' ])
               (d : D .ob)
             → ProdAx

  private
    Q : Quiver _ _
    Q .ob = C .ob × D .ob
    Q .mor = ProdGenerator
    Q .dom (_×ₑ_ {c = c}{d = d} _ _) = c , d
    Q .cod (_×ₑ_ {c' = c'}{d' = d'} _ _) = c' , d'
    Q .dom (_id×_ c {d = d} g) = c , d
    Q .cod (_id×_ c {d' = d'} g) = c , d'
    Q .dom (_×id_ {c = c} f d) = c , d
    Q .cod (_×id_ {c' = c'} f d) = c' , d

    Ax : Axioms Q _
    Ax = mkAx Q ProdAx λ
      { (combine-id×id {c = c}{c' = c'}{d = d}{d' = d'} f g) → _ , _ ,
        η Q .I-hom (c' id× g) ∘⟨ FreeCat Q ⟩ η Q .I-hom (f ×id d)
        , η Q .I-hom (f ×ₑ g)
      ; (combine-×id× {c = c}{c' = c'}{d = d}{d' = d'} f g) → _ , _ ,
        η Q .I-hom (f ×id d') ∘⟨ FreeCat Q ⟩ η Q .I-hom (c id× g)
        , η Q .I-hom (f ×ₑ g)
      ; (id×-Id c d) → _ , _ ,
          (η Q .I-hom (c id× D .id {d}))
          , (FreeCat Q .id)
      ; (id×-Comp c g' g) → _ , _ ,
          η Q .I-hom (c id× (g' ∘⟨ D ⟩ g))
          , η Q .I-hom (c id× g') ∘⟨ FreeCat Q ⟩ η Q .I-hom (c id× g)
      ; (×id-Id c d) → _ , _ ,
          η Q .I-hom ((C .id {c}) ×id d)
          , FreeCat Q .id
      ; (×id-Comp f' f d) → _ , _ ,
          η Q .I-hom ((f' ∘⟨ C ⟩ f) ×id d)
          , η Q .I-hom (f' ×id d) ∘⟨ FreeCat Q ⟩ η Q .I-hom (f ×id d)
      }

  _×C_ : Category _ _
  _×C_ = PresentedCat Q Ax

  open Bifunctor
  ×l : (c : C .ob) → Functor D _×C_
  ×l c .F-ob d = c , d
  ×l c .F-hom g = ηP Q Ax .I-hom (c id× g)
  ×l c .F-id {d} = ηEq Q Ax (id×-Id c d)
  ×l c .F-seq g g' = ηEq Q Ax (id×-Comp c g' g)

  ×r : (d : D .ob) → Functor C _×C_
  ×r d .F-ob c = c , d
  ×r d .F-hom f = ηP Q Ax .I-hom (f ×id d)
  ×r d .F-id {c} = ηEq Q Ax (×id-Id c d)
  ×r d .F-seq f f' = ηEq Q Ax (×id-Comp f' f d)

  -- UniversalBifunctor : Bifunctor C D _×C_
  -- UniversalBifunctor .Bif-ob = _,_
  -- UniversalBifunctor .Bif-homL f d = ×r d ⟪ f ⟫
  -- UniversalBifunctor .Bif-homR c g = ×l c ⟪ g ⟫
  -- UniversalBifunctor .Bif-idL = ×r _ .F-id
  -- UniversalBifunctor .Bif-idR = ×l _ .F-id
  -- UniversalBifunctor .Bif-seqL f f' = ×r _ .F-seq f f'
  -- UniversalBifunctor .Bif-seqR g g' = ×l _ .F-seq g g'
  -- UniversalBifunctor .Bif-assoc f g = ηEq Q Ax (commute f g)
