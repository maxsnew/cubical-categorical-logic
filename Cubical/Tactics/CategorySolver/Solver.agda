{-# OPTIONS --safe #-}
module Cubical.Tactics.CategorySolver.Solver where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Yoneda
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf

open import Cubical.Categories.Constructions.Free.General
open import Cubical.Categories.Yoneda.More

private
  variable
    ℓ ℓ' : Level
open Category
open Functor

module Eval (𝓒 : Category ℓ ℓ') where
  -- Semantics in 𝓒 itself, tautologically
  sem𝓒 = ϵ {𝓒 = 𝓒}
  ⟦_⟧c = sem𝓒 .F-hom
  -- Semantics in 𝓟o 𝓒, interpreting fun symbols using Yoneda
  semYo = Semantics.sem (Ugr 𝓒) (PresheafCategory 𝓒 ℓ') (Uhom (YONEDA {C = 𝓒}))
  ⟦_⟧yo = semYo .F-hom
  
  -- | Evaluate by taking the semantics in 𝓟 𝓒 and
  -- | use the Yoneda lemma to extract a morphism in 𝓒.
  eval : ∀ {A B} → FreeCat (Ugr 𝓒) [ A , B ] → 𝓒 [ A , B ]
  eval {A}{B} e = Iso.fun (yonedaᴾ {C = 𝓒} (𝓒 [-, B ]) A) ⟦ e ⟧yo


  -- | Eval agrees with the tautological semantics
  -- | There is a more direct proof but this one generalizes better
  solve : ∀ {A B} → (e₁ e₂ : FreeCat (Ugr 𝓒) [ A , B ])
        → eval e₁ ≡ eval e₂
        → ⟦ e₁ ⟧c ≡ ⟦ e₂ ⟧c
  solve {A}{B} e₁ e₂ p = isFaithfulYoneda _ _ _ _ yo∘c≡ where
    yo≡ : ⟦ e₁ ⟧yo ≡ ⟦ e₂ ⟧yo
    yo≡ = isoFunInjective ((yonedaᴾ {C = 𝓒} (𝓒 [-, _ ]) _)) _ _ p

    commutes : ∀ (e : FreeCat (Ugr 𝓒) [ A , B ]) → ⟦ e ⟧yo ≡ YONEDA ⟪ ⟦ e ⟧c ⟫
    commutes e = sym (uniq-on-morphisms (Ugr 𝓒) (YONEDA {C = 𝓒} ∘F sem𝓒) e)

    yo∘c≡ : YONEDA {C = 𝓒} ⟪ ⟦ e₁ ⟧c ⟫ ≡ YONEDA ⟪ ⟦ e₂ ⟧c ⟫
    yo∘c≡ = sym (commutes e₁) ∙ yo≡ ∙ commutes e₂

solve : (𝓒 : Category ℓ ℓ')
      → {A B : 𝓒 .ob}
      → (e₁ e₂ : FreeCat (Ugr 𝓒) [ A , B ])
      → (p : Eval.eval 𝓒 e₁ ≡ Eval.eval 𝓒 e₂)
      → _
solve = Eval.solve
