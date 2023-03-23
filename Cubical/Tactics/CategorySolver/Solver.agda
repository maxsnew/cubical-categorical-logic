{-# OPTIONS --safe #-}
module Cubical.Tactics.CategorySolver.Solver where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category

private
  variable
    ℓ ℓ' : Level
open Category

-- | A type theoretic gloss on the free category
module _ (C : Category ℓ ℓ') where
  BaseTy = C .ob
  FunSym = C .Hom[_,_]
  data UTT (Γ : BaseTy) : BaseTy → Type (ℓ-max ℓ ℓ') where
    var : UTT Γ Γ
    app : ∀ {A B} → FunSym A B → UTT Γ A → UTT Γ B

  data Exp : BaseTy → BaseTy → Type (ℓ-max ℓ ℓ') where
    idₑ  : ∀ {Γ} → Exp Γ Γ
    _⋆ₑ_ : ∀ {A B C} → Exp A B → Exp B C → Exp A C
    ↑_   : ∀ {A B} → FunSym A B → Exp A B

module Eval (𝓒 : Category ℓ ℓ') where
  open Category 𝓒

  ⟦_⟧ : ∀ {A B} → Exp 𝓒 A B → 𝓒 [ A , B ]
  ⟦ idₑ ⟧ =  𝓒 .id
  ⟦ e ⋆ₑ e' ⟧ = ⟦ e ⟧ ⋆⟨ 𝓒 ⟩ ⟦ e' ⟧
  ⟦ ↑ f ⟧ = f

  NormalForm = UTT

  _⟨_⟩ : ∀ {A B C} → NormalForm 𝓒 B C → NormalForm 𝓒 A B → NormalForm 𝓒 A C
  var ⟨ γ ⟩ = γ
  app f t ⟨ γ ⟩ = app f (t ⟨ γ ⟩)

  normalize : ∀ {A B} → Exp 𝓒 A B → NormalForm 𝓒 A B
  normalize idₑ = var
  normalize (e ⋆ₑ e₁) = normalize e₁ ⟨ normalize e ⟩
  normalize (↑ f) = app f var

  eval : ∀ {A B} → NormalForm 𝓒 A B → 𝓒 [ A , B ]
  eval var = 𝓒 .id 
  eval (app f t) = eval t ⋆⟨ 𝓒 ⟩ f

  evalHomomorphism : ∀ {A B C} → (t : NormalForm 𝓒 B C) → (γ : NormalForm 𝓒 A B)
           → eval (t ⟨ γ ⟩) ≡ eval γ ⋆⟨ 𝓒 ⟩ eval t
  evalHomomorphism var γ = sym (𝓒 .⋆IdR _)
  evalHomomorphism (app f t) γ =
    (λ i → f ∘⟨ 𝓒 ⟩ evalHomomorphism t γ i )
    ∙ 𝓒 .⋆Assoc _ _ _

module EqualityToNormalForm (𝓒 : Category ℓ ℓ') where
  open Eval 𝓒
  open Category 𝓒

  isEqualToNormalForm : ∀ {A B}
                      → (e : Exp 𝓒 A B)
                      → eval (normalize e) ≡ ⟦ e ⟧
  isEqualToNormalForm idₑ = refl
  isEqualToNormalForm (e ⋆ₑ e₁) = evalHomomorphism (normalize e₁) (normalize e) ∙ λ i → isEqualToNormalForm e i ⋆⟨ 𝓒 ⟩ isEqualToNormalForm e₁ i
  isEqualToNormalForm (↑ _) = 𝓒 .⋆IdL _

  solve : ∀ {A B} → (e₁ e₂ : Exp 𝓒 A B)
        → eval (normalize e₁) ≡ eval (normalize e₂)
        → ⟦ e₁ ⟧ ≡ ⟦ e₂ ⟧
  solve e₁ e₂ p = sym (isEqualToNormalForm e₁) ∙ p ∙ isEqualToNormalForm e₂

solve : (𝓒 : Category ℓ ℓ')
      → {A B : 𝓒 .ob}
      → (e₁ e₂ : Exp 𝓒 A B)
      → (p : Eval.eval 𝓒 (Eval.normalize 𝓒 e₁) ≡ Eval.eval 𝓒 (Eval.normalize 𝓒 e₂))
      → _
solve = EqualityToNormalForm.solve
