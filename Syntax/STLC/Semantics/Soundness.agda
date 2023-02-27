module Syntax.STLC.Semantics.Soundness where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf

open import NamedContext
open import UMP
open import NaturalModels.Cartesian
open import Syntax.STLC renaming (Tm to STm; Ty to STy)
open import Syntax.STLC.Semantics.Interpretation
open import Syntax.STLC.Semantics.Lindenbaum

private
  variable
    ℓ ℓ' ℓb ℓb' ℓc ℓc' ℓt ℓt' : Level
module _ {Σ₀ : Sig₀ ℓ}{Σ₁ : Sig₁ Σ₀ ℓ'}
         (S : SimplyTypedCategory ℓb ℓb' ℓt ℓt')
         (i₀ : Interp₀ Σ₀ S) (i₁ : Interp₁ {S = S} i₀ Σ₁)
         where
  open Category
  open SimplyTypedCategory
  open STC-Functor
  open CartesianFunctor
  open CartesianCategory
  open UnivElt
  open isUniversal
  open Ctx
  open Sig₁

  ctx-sem : Ctx (STy Σ₀) → S .B .cat .ob
  ctx-sem Γ =
    S .B .finite-products ((Γ .var) , (Γ .isFinSetVar)) (λ x → sole S (i₀ (Γ .el x))) .vertex

  term-sem : ∀ {Γ A} → STm {Σ₀ = Σ₀} Σ₁ Γ A → (S .Tm (i₀ A) ⟅ ctx-sem Γ ⟆) .fst
  term-sem (ivar x) = S .B .cat [ S .Tm-repr _ .element ∘ᴾ⟨ S .Tm _ ⟩ π (S .B) _ _ x ]
  term-sem (fun-app f γ) = S .B .cat [ i₁ f ∘ᴾ⟨ S .Tm _ ⟩ S .B .finite-products ((Σ₁ .src f .var) , (Σ₁ .src f .isFinSetVar)) (λ x → sole S (i₀ (Σ₁ .src f .el x))) .universal .coinduction (λ j → _/var S (term-sem (γ j))) ]

  -- Soundness says that we can translate any structure in the
  -- Lindenbaum algebra homomorphically into any CT structure.
  soundness : STC-Functor (Lindenbaum {Σ₀ = Σ₀}{Σ₁ = Σ₁}) S
  soundness .F-B .func .Functor.F-ob Γ = ctx-sem Γ
  soundness .F-B .func .Functor.F-hom = {!!}
  soundness .F-B .func .Functor.F-id = {!!}
  soundness .F-B .func .Functor.F-seq = {!!}
  soundness .F-B .preserves-terminal = {!!}
  soundness .F-B .preserves-products = {!!}
  soundness .F-Ty = i₀
  soundness .F-Tm A .NatTrans.N-ob Γ (lift M) = lift {!M!} where
    
  soundness .F-Tm A .NatTrans.N-hom = {!!}
  soundness .F-Tm-repr = {!!}

