{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Tactics.FunctorSolver.Solver where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Id renaming (refl to reflId) hiding (_∙_)
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function renaming (_∘_ to _∘f_)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor renaming (Id to IdF)
open import Cubical.Categories.NaturalTransformation
open import Cubical.Data.Graph.Base
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Instances.Sets

open import Cubical.Categories.Constructions.Free.General as FreeCat
open import Cubical.Categories.Constructions.Free.Functor as FreeFunctor
open import Cubical.Categories.Constructions.Free.UnderlyingGraph
open import Cubical.Data.Graph.Properties
open import Cubical.Categories.Yoneda.More
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Tactics.CategorySolver.Reflection

open import Cubical.Categories.Constructions.Power

private
  variable
    ℓc ℓc' ℓd ℓd' ℓb ℓb' : Level
open Category
open Functor
open NatIso
open NatTrans

module Eval (𝓒 : Category ℓc ℓc') (𝓓 : Category ℓd ℓd')  (𝓕 : Functor 𝓒 𝓓) where
  -- category of 𝓒 expressions
  -- TODO: refactor to use named module
  Free𝓒 = FG (Ugr 𝓒) (Ugr 𝓓) (𝓕 .F-ob)
  η𝓒 = ηG (Ugr 𝓒) (Ugr 𝓓) (𝓕 .F-ob)
  Free𝓓 : Category ℓd (ℓ-max (ℓ-max (ℓ-max ℓc ℓc') ℓd) ℓd')
  η𝓓 = ηH (Ugr 𝓒) (Ugr 𝓓) (𝓕 .F-ob)
  Free𝓓 = FH (Ugr 𝓒) (Ugr 𝓓) (𝓕 .F-ob)
  Free𝓕 = Fϕ (Ugr 𝓒) (Ugr 𝓓) (𝓕 .F-ob)
  𝓟 = PowerCategoryS (Free𝓓 .ob) (ℓ-max (ℓ-max (ℓ-max ℓc ℓc') ℓd) ℓd')
  PsYo : Functor Free𝓓 𝓟
  PsYo = PseudoYonedaS {C = Free𝓓}

  module TautoSem = FreeFunctor.Semantics (Ugr 𝓒) (Ugr 𝓓) (𝓕 .F-ob) {𝓒 = 𝓒} {𝓓 = 𝓓} {𝓕 = 𝓕} IdHom IdHom reflId
  module YoSem = FreeFunctor.Semantics (Ugr 𝓒) (Ugr 𝓓) (𝓕 .F-ob) {𝓒 = 𝓟} {𝓓 = 𝓟} {𝓕 = IdF}
                   (Uhom (PsYo ∘F Free𝓕) ∘GrHom η𝓒)
                   (Uhom           PsYo  ∘GrHom η𝓓)
                   reflId

  eval : ∀ {A B} → Free𝓓 [ A , B ] → _
  eval {A}{B} e = YoSem.semH ⟪ e ⟫

  Yo-YoSem-Agree : Path _ PsYo YoSem.semH
  Yo-YoSem-Agree = sem-uniq-H where
    open YoSem.Uniqueness (PsYo ∘F Free𝓕) PsYo F-rUnit refl refl
           (compPath→Square (symPath (lUnit (idToPath reflId))
                            ∙ idToPathRefl
                            ∙ rUnit refl))
  solve : ∀ {A B}
        → (e e' : Free𝓓 [ A , B ])
        → (p : Path _ (YoSem.semH ⟪ e ⟫) (YoSem.semH ⟪ e' ⟫))
        → Path _ (TautoSem.semH ⟪ e ⟫) (TautoSem.semH ⟪ e' ⟫)
  solve {A}{B} e e' p = congPath (TautoSem.semH .F-hom) (isFaithfulPseudoYonedaS _ _ _ _ lem) where
    lem : Path _ (PsYo ⟪ e ⟫) (PsYo ⟪ e' ⟫)
    lem = transportPath (λ i → Path _ (Yo-YoSem-Agree (~ i) ⟪ e ⟫) (Yo-YoSem-Agree (~ i) ⟪ e' ⟫)) p

solve = Eval.solve
