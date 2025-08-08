{-# OPTIONS --safe --lossy-unification #-}
{-
  Displayed and Vertical Exponentials

  Displayed Exponentials are fairly straightforward but Vertical Exponentials
  are less nice. Here we have defined them in the textbook way: exponential in
  each fiber that's preserved by reindexing.
-}
module Cubical.Categories.Displayed.Exponentials.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

-- open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Exponentials
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.TotalCategory as TC
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Limits.BinProduct.Base
open import Cubical.Categories.Displayed.Limits.BinProduct.Properties
open import Cubical.Categories.Displayed.Limits.BinProduct.Fiberwise
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Fibration.Properties
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Quantifiers
open import Cubical.Categories.Displayed.Constructions.Reindex.Base as Reindex
import Cubical.Categories.Displayed.Reasoning as Reasoning

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module Cᴰ = Categoryᴰ Cᴰ
  Exponentialᴰ :
    ∀ {c d} { -×c : BinProductsWith C c}
    cᴰ (dᴰ : Cᴰ.ob[ d ]) (-×ᴰcᴰ : BinProductsWithᴰ Cᴰ -×c cᴰ)
    → (c⇒d : Exponential C c d -×c)
    → Type _
  Exponentialᴰ cᴰ dᴰ -×ᴰcᴰ c⇒d = RightAdjointAtᴰ (BinProductWithFᴰ Cᴰ _ -×ᴰcᴰ) c⇒d dᴰ

  Exponentialsᴰ : ∀ bp
    → Exponentials C bp
    → BinProductsᴰ Cᴰ bp
    → Type _
  Exponentialsᴰ bp exps bpᴰ = ∀ {c d} (cᴰ : Cᴰ.ob[ c ])(dᴰ : Cᴰ.ob[ d ])
    → Exponentialᴰ cᴰ dᴰ (λ _ xᴰ → bpᴰ (xᴰ , cᴰ)) (AnExponential C bp exps)

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
  module _ (bpⱽ : BinProductsⱽ Cᴰ) (cartesianLifts : isFibration Cᴰ)
    where

    record Exponentialⱽ {c : C.ob} (cᴰ cᴰ' : Cᴰ.ob[ c ]) : Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) ℓCᴰ') where
      no-eta-equality
      field
        cᴰ⇒cᴰ' : Exponential Cᴰ.v[ c ] cᴰ cᴰ'
          (BinProductsWithⱽ→BinProductsWithFiber Cᴰ λ _ → bpⱽ _ _)
        reindex⇒ : ∀ {b} (f : C [ b , c ])
          → preservesExponential (CartesianLiftF-fiber Cᴰ cartesianLifts f)
            (BinProductsWithⱽ→BinProductsWithFiber Cᴰ λ cᴰ'' → bpⱽ _ _)
            (λ _ → cartesianLift-preserves-BinProductFiber Cᴰ cartesianLifts (bpⱽ _ _) f)
            (BinProductsWithⱽ→BinProductsWithFiber Cᴰ λ cᴰ'' → bpⱽ _ _)
            cᴰ⇒cᴰ'

    Exponentialsⱽ : Type _
    Exponentialsⱽ = ∀ {c} cᴰ cᴰ' → Exponentialⱽ {c} cᴰ cᴰ'


module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') (bp : BinProducts C)
    (bpⱽ : BinProductsⱽ Cᴰ)
    (cartesianLifts : isFibration Cᴰ)
  where

  private
    module C = Category C
    module Cᴰ = Categoryᴰ Cᴰ
    module Fibs = Fibers Cᴰ
    bpᴰ : BinProductsᴰ Cᴰ bp
    bpᴰ = BinProductsⱽ→BinProductsᴰ Cᴰ cartesianLifts bpⱽ bp
    isFib' = isFibration→isFibration' cartesianLifts

  module bp = BinProductsNotation bp
  open bp
  module bpⱽ = BinProductsⱽNotation Cᴰ bpⱽ
  open bpⱽ
  module bpᴰ = BinProductsᴰNotation bpᴰ
  open CartesianLift
  open Functor
  open Functorᴰ
  open Exponentialⱽ
  open UniversalElementᴰ
  open UniversalElementⱽ

  module _
    {c d : C.ob}{p : Cᴰ.ob[ c × d ]}
    {cᴰ : Cᴰ.ob[ c ]} {dᴰ : Cᴰ.ob[ d ]}
    (exp : Exponential C c d (λ c' → bp (c' , c)))
    where

    module c⇒d = ExponentialNotation _ exp

    module c⇒d×c = BinProductNotation (bp (c⇒d.vert , c))

    π₂*cᴰCL = cartesianLifts cᴰ c⇒d×c.π₂
    module π₂*cᴰ = CartesianLift π₂*cᴰCL

    app*dᴰCL = cartesianLifts dᴰ c⇒d.app
    module app*dᴰ = CartesianLift app*dᴰCL

    module _
      (expⱽ : Exponentialⱽ Cᴰ bpⱽ cartesianLifts π₂*cᴰ.f*yᴰ app*dᴰ.f*yᴰ)
      where

      module π₂*cᴰ⇒app*dᴰ = ExponentialNotation _ (expⱽ .cᴰ⇒cᴰ')

      module _
        (uq : UniversalQuantifier bp isFib' π₂*cᴰ⇒app*dᴰ.vert)
        where

        ExpPshᴰ = RightAdjointProfᴰ (BinProductWithFᴰ Cᴰ (λ c' → bp (c' , c)) (λ c' cᴰ' → bpᴰ (cᴰ' , cᴰ))) .F-obᴰ dᴰ
        open PresheafᴰNotation ExpPshᴰ

        module π₁*uq = CartesianLift (cartesianLifts (uq .vertexⱽ) c⇒d×c.π₁)

        -- TODO name
        x : Exponentialᴰ Cᴰ cᴰ dᴰ (λ c' cᴰ' → bpᴰ (cᴰ' , cᴰ)) exp
        x .vertexᴰ = uq .vertexⱽ
        x .elementᴰ = y
          where
          -- What actually is uq?
          -- What is the effect of the choice of binary products bpᴰ?

          _ : bpᴰ (uq .vertexⱽ , cᴰ) .vertexᴰ ≡ bpⱽ _ (π₁*uq.f*yᴰ , π₂*cᴰ.f*yᴰ) .vertexⱽ
          _ = refl

          weak : Cᴰ.ob[ c⇒d.vert × c ]
          weak = weakenⱽ bp isFib' .F-obᴰ (uq .vertexⱽ)

          -- As I'm attempting this proof, I need a map between the pullback by π₁
          -- via CartesianLift and weak (which is defined using CartesianLift')
          -- However, I don't think I actually want a morphism here, rather
          -- the defintion of the universal quantifier should be augmented so that
          -- weakening is defintionally the same as π₁*
          weak→ : Cᴰ [ C.id ][ π₁*uq.f*yᴰ , weak ]
          weak→ = {!!}

          weak≡ : weak ≡ (CartesianLift'F Cᴰ isFib' ∘Fⱽᴰ (π₁Fᴰ bp isFib')) .F-obᴰ (uq .vertexⱽ)
          weak≡ = refl

          elt : Cᴰ [ BinProductF' _ bp .F-hom ((C ×C C) .Category.id) ][ weak , π₂*cᴰ⇒app*dᴰ.vert ]
          elt = uq .elementⱽ

          elt' : Cᴰ [ C.id ][ weak , π₂*cᴰ⇒app*dᴰ.vert ]
          elt' = Reasoning.reind Cᴰ (BinProductF' C bp .F-id) elt


          q : Cᴰ [ {!!} ][ π₁*uq.f*yᴰ , weak ]
          q = weak→
            -- π₁*uq.π Cᴰ.⋆ᴰ {!!}


          u : Cᴰ [ {!!} ][ π₁*uq.f*yᴰ , π₂*cᴰ⇒app*dᴰ.vert ]
          u = {!!}
            -- π₂*cᴰ⇒app*dᴰ.lda {!uq .elementⱽ!}
                -- ({!!} ⋆⟨ Fibs.v[ c⇒d×c.vert ] ⟩ π₂*cᴰ⇒app*dᴰ.app)

          z : Cᴰ [ {!!} C.⋆ C.id C.⋆ c⇒d.app ][ π₁*uq.f*yᴰ ×ⱽ π₂*cᴰ.f*yᴰ , dᴰ ]
          z = ((bpⱽ.π₁ Cᴰ.⋆ᴰ u) ,ⱽ (bpⱽ.π₂ Cᴰ.⋆ᴰ {!!})) Cᴰ.⋆ᴰ π₂*cᴰ⇒app*dᴰ.app Cᴰ.⋆ᴰ app*dᴰ.π

          y : Cᴰ [ c⇒d.app ][ π₁*uq.f*yᴰ ×ⱽ π₂*cᴰ.f*yᴰ , dᴰ ]
          y = {!!}
        x .universalᴰ = {!!}


-- module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
--   (bp : BinProducts C)
--   (bpⱽ : BinProductsⱽ Cᴰ) (cartesianLifts : isFibration Cᴰ)
--   (expⱽ : Exponentialsⱽ Cᴰ bpⱽ cartesianLifts)
--   (∀s : UniversalQuantifiers bp (isFibration→isFibration' cartesianLifts))
--   where

--   Exponentialⱽ+UniversalQuantifier→Exponentialᴰ : Exponentialᴰ Cᴰ ? ?
