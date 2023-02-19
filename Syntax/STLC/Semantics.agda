module Syntax.STLC.Semantics where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Fin
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Constructions.Elements
open import Cubical.Categories.Limits.Terminal
open import Cubical.Data.Sigma
open import Cubical.Foundations.HLevels
open import Cubical.Data.Fin

open import Syntax.STLC renaming (Tm to Term)
open import NaturalModels.Cartesian
open import Context hiding (_[_])

open Functor

module _ {ℓ}{Σ₀ : Sig₀ ℓ}{Σ₁ : Sig₁ Σ₀} where
  open Category
  open SimplyTypedCategory

  STTCtx : Category ℓ ℓ
  STTCtx .ob = ICtx (Ty Σ₀)
  STTCtx .Hom[_,_] Δ Γ = isubstitution (Term Σ₁ Δ) Γ -- substitution (Term Σ₁ Δ) Γ
  STTCtx .id = id-subst _
  STTCtx ._⋆_ = λ δ γ → comp-subst γ δ
  STTCtx .⋆IdL = comp-subst-IdInp
  STTCtx .⋆IdR = comp-subst-IdOutp
  STTCtx .⋆Assoc = λ f g h → comp-subst-Assoc h g f
  STTCtx .isSetHom = isSetTTProof.isSetSubst Σ₀ Σ₁ _ _

  Tm-presheaf : ∀ A → Presheaf STTCtx ℓ
  Tm-presheaf A .F-ob Γ = (Term Σ₁ Γ A) , isSetTTProof.isSetTm Σ₀ Σ₁ Γ A
  Tm-presheaf A .F-hom = λ γ M → M ⟨ γ ⟩
  Tm-presheaf A .F-id = funExt subst-idInp
  Tm-presheaf A .F-seq γ δ = funExt λ M → subst-Assoc M γ δ

  completeness : SimplyTypedCategory ℓ ℓ
  completeness .B = STTCtx
  completeness .· = iempty-ctx _ , λ Γ → !-subst Γ , !-subst-uniq Γ where
    !-subst : ∀ Γ → STTCtx [ Γ , iempty-ctx _ ]
    !-subst Γ = λ x → rec (¬Fin0 (x .snd))

    !-subst-uniq : ∀ Γ (!' : STTCtx [ Γ , iempty-ctx (Ty Σ₀) ]) → !-subst Γ ≡ !'
    !-subst-uniq Γ !' = funExt (λ x → rec (¬Fin0 (x .snd)))
  completeness ._,,_ = {!!}
  completeness .Ob = Ty Σ₀
  completeness .Tm = Tm-presheaf
  completeness .Tm-repr A = UniversalElementToRepresentation STTCtx (Tm-presheaf A) (({!!} , {!!}) , {!!}) where
    
