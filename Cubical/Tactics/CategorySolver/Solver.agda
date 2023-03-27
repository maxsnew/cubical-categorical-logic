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
  module Tauto = Semantics (Ugr 𝓒) 𝓒 (Uhom (Id {C = 𝓒}))
  -- Semantics in 𝓟o 𝓒, interpreting fun symbols using Yoneda
  module Yo    = Semantics (Ugr 𝓒) (PresheafCategory 𝓒 ℓ') (Uhom (YONEDA {C = 𝓒}))
  
  -- | Evaluate by taking the semantics in 𝓟 𝓒 and
  -- | use the Yoneda lemma to extract a morphism in 𝓒.
  eval : ∀ {A B} → FreeCat (Ugr 𝓒) [ A , B ] → 𝓒 [ A , B ]
  eval {A}{B} e = Iso.fun (yonedaᴾ {C = 𝓒} (𝓒 [-, B ]) A) Yo.⟦ e ⟧

  -- | Eval agrees with the tautological semantics
  isEqualToNormalForm : ∀ {A B}
                      → (e : FreeCat (Ugr 𝓒) [ A , B ])
                      → eval e ≡ Tauto.⟦ e ⟧
  isEqualToNormalForm {A}{B} e =
    Iso.fun (yonedaᴾ {C = 𝓒} (𝓒 [-, _ ]) _) Yo.⟦ e ⟧
      ≡[ i ]⟨ Iso.fun (yonedaᴾ {C = 𝓒} (𝓒 [-, _ ]) _) (lemma i) ⟩
    Iso.fun (yonedaᴾ {C = 𝓒} (𝓒 [-, _ ]) _) (YONEDA ⟪ Tauto.⟦ e ⟧ ⟫)
      ≡⟨ Iso.rightInv (yonedaᴾ {C = 𝓒} (𝓒 [-, _ ]) _) Tauto.⟦ e ⟧ ⟩
    Tauto.⟦ e ⟧ ∎
    where
      lemma : Yo.⟦ e ⟧ ≡ YONEDA ⟪ Tauto.⟦ e ⟧ ⟫
      lemma = sym (uniq-on-morphisms (Ugr 𝓒) (YONEDA {C = 𝓒} ∘F Tauto.sem) e)

  solve : ∀ {A B} → (e₁ e₂ : FreeCat (Ugr 𝓒) [ A , B ])
        → eval e₁ ≡ eval e₂
        → Tauto.⟦ e₁ ⟧ ≡ Tauto.⟦ e₂ ⟧
  solve e₁ e₂ p = sym (isEqualToNormalForm e₁) ∙ p ∙ isEqualToNormalForm e₂

solve : (𝓒 : Category ℓ ℓ')
      → {A B : 𝓒 .ob}
      → (e₁ e₂ : FreeCat (Ugr 𝓒) [ A , B ])
      → (p : Eval.eval 𝓒 e₁ ≡ Eval.eval 𝓒 e₂)
      → _
solve = Eval.solve
