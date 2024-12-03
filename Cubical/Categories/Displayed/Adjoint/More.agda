{-
  Definition of an adjoint pair displayed over another adjoint pair
-}
{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Adjoint.More where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Profunctor.Hom
open import Cubical.Categories.Yoneda
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Instances.Functor
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Presheaf

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category
open Categoryᴰ
open Functorᴰ

RightAdjointProfᴰ : {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
                  {F : Functor C D}
                  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
                  (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
  → Functorᴰ (RightAdjointProf F) Dᴰ (FUNCTORᴰ (Cᴰ ^opᴰ) (SETᴰ ℓD' ℓDᴰ'))
RightAdjointProfᴰ Fᴰ = precomposeFᴰ _ _ (Fᴰ ^opFᴰ) ∘Fᴰ YOᴰ

RightAdjointAtᴰ : {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
                  {F : Functor C D}
                  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
                  (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
                  {d : D .ob}
                  (R⟅d⟆ : RightAdjointAt F d)
                  (dᴰ : Categoryᴰ.ob[_] Dᴰ d)
                → Type _
RightAdjointAtᴰ {Cᴰ = Cᴰ}{Dᴰ = Dᴰ} Fᴰ R⟅d⟆ dᴰ =
  UniversalElementᴰ Cᴰ (RightAdjointProfᴰ Fᴰ .F-obᴰ dᴰ) R⟅d⟆

RightAdjointᴰ : {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
                {F : Functor C D}
                {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
                (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
                (R : RightAdjoint F)
              → Type _
RightAdjointᴰ Fᴰ R = ∀ {d} dᴰ → RightAdjointAtᴰ Fᴰ (R d) dᴰ

RightAdjointProfᵛ : {C : Category ℓC ℓC'}
                  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ C ℓDᴰ ℓDᴰ'}
                  (Fᵛ : Functorᵛ Cᴰ Dᴰ)
  → Functorᴰ (YO {C = C}) Dᴰ (FUNCTORᴰ (Cᴰ ^opᴰ) (SETᴰ ℓC' ℓDᴰ'))
RightAdjointProfᵛ Fᵛ = precomposeFᵛ _ _ (Fᵛ ^opFᵛ) ∘Fᵛᴰ YOᴰ

VerticalRightAdjointAtᴰ : {C : Category ℓC ℓC'}
                     {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ C ℓDᴰ ℓDᴰ'}
                     (Fᵛ : Functorᵛ Cᴰ Dᴰ)
                     {c : C .ob}
                     (dᴰ : Categoryᴰ.ob[_] Dᴰ c)
                     → Type _
VerticalRightAdjointAtᴰ {Cᴰ = Cᴰ} Fᵛ {c} dᴰ =
  UniversalElementᵛ Cᴰ c (RightAdjointProfᵛ Fᵛ .F-obᴰ dᴰ)

VerticalRightAdjointᴰ : {C : Category ℓC ℓC'}
                     {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ C ℓDᴰ ℓDᴰ'}
                     (Fᵛ : Functorᵛ Cᴰ Dᴰ)
                   → Type _
VerticalRightAdjointᴰ Fᵛ = ∀ {x} xᴰ → VerticalRightAdjointAtᴰ Fᵛ {x} xᴰ
