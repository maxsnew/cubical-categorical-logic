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
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent

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
open import Cubical.Categories.Displayed.FunctorComprehension
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
  open bpⱽ hiding (introⱽ)
  module bpᴰ = BinProductsᴰNotation bpᴰ
  open CartesianLift
  open Functor
  open Functorᴰ
  open Exponentialⱽ
  open UniversalElementᴰ
  open UniversalElementⱽ

  module _
    {c d : C.ob}
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
        module ExpPshᴰ = PresheafᴰNotation ExpPshᴰ

        π₁*uqCL = cartesianLifts (uq .vertexⱽ) c⇒d×c.π₁
        module π₁*uq = CartesianLift π₁*uqCL

        -- TODO name
        Exponentialⱽ+UniversalQuanitier→Exponentialᴰ : Exponentialᴰ Cᴰ cᴰ dᴰ (λ c' cᴰ' → bpᴰ (cᴰ' , cᴰ)) exp
        Exponentialⱽ+UniversalQuanitier→Exponentialᴰ .vertexᴰ = uq .vertexⱽ
        Exponentialⱽ+UniversalQuanitier→Exponentialᴰ  .elementᴰ = the-elt
          where
          weak : Cᴰ.ob[ c⇒d.vert × c ]
          weak = weakenⱽ bp isFib' .F-obᴰ (uq .vertexⱽ)

          weak≡ : weak ≡ π₁*uq.f*yᴰ
          weak≡ = sym $ FunctorⱽComprehension-ob-filler _ _

          f : Cᴰ [ C.id ][ π₁*uq.f*yᴰ , π₂*cᴰ⇒app*dᴰ.vert ]
          f = subst (λ z → Cᴰ [ C.id ][ z , π₂*cᴰ⇒app*dᴰ.vert ]) weak≡
                      (Reasoning.reind Cᴰ (BinProductF' C bp .F-id) (uq .elementⱽ))

          g : Cᴰ [ (C.id C.⋆ _) C.⋆ C.id C.⋆ c⇒d.app ][ π₁*uq.f*yᴰ ×ⱽ π₂*cᴰ.f*yᴰ , dᴰ ]
          g = ((bpⱽ.π₁ Cᴰ.⋆ᴰ f) ,ⱽ (bpⱽ.π₂ Cᴰ.⋆ᴰ Cᴰ.idᴰ)) Cᴰ.⋆ᴰ π₂*cᴰ⇒app*dᴰ.app Cᴰ.⋆ᴰ app*dᴰ.π

          the-elt : Cᴰ [ c⇒d.app ][ π₁*uq.f*yᴰ ×ⱽ π₂*cᴰ.f*yᴰ , dᴰ ]
          the-elt =
            Reasoning.reind Cᴰ
              ((λ i → C.⋆IdL C.id i C.⋆ C.id C.⋆ c⇒d.app)
              ∙ C.⋆IdL _
              ∙ C.⋆IdL _)
              g
        Exponentialⱽ+UniversalQuanitier→Exponentialᴰ .universalᴰ .isIsoOver.inv f x =
          {!uq .universalⱽ .fst !}
        Exponentialⱽ+UniversalQuanitier→Exponentialᴰ .universalᴰ .isIsoOver.rightInv = {!!}
        Exponentialⱽ+UniversalQuanitier→Exponentialᴰ .universalᴰ .isIsoOver.leftInv = {!!}
