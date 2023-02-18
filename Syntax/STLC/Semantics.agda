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
open import Context

open Functor

module _ {ℓ}{Σ₀ : Sig₀ ℓ}{Σ₁ : Sig₁ Σ₀} where
  open Category
  open SimplyTypedCategory

  STTCtx : Category ℓ ℓ
  STTCtx .ob = Ctx (Ty Σ₀)
  STTCtx .Hom[_,_] Δ Γ = substitution (Term Σ₁ Δ) Γ
  STTCtx .id = var
  STTCtx ._⋆_ = λ δ γ → comp-subst γ δ
  STTCtx .⋆IdL = comp-subst-IdInp
  STTCtx .⋆IdR = comp-subst-IdOutp
  STTCtx .⋆Assoc = λ f g h → comp-subst-Assoc h g f
  STTCtx .isSetHom = {!!}

  Tm-presheaf : ∀ A → Presheaf STTCtx ℓ
  Tm-presheaf A .F-ob Γ = (Term Σ₁ Γ A) , {!!}
  Tm-presheaf A .F-hom = λ γ M → M ⟨ γ ⟩
  Tm-presheaf A .F-id = funExt subst-idInp
  Tm-presheaf A .F-seq γ δ = funExt λ M → subst-Assoc M γ δ

  completeness : SimplyTypedCategory ℓ ℓ
  completeness .B = STTCtx
  completeness .· = empty-ctx (Ty Σ₀) , λ Γ → the-subst , the-only-subst where
    the-subst : ∀ {Γ} → substitution (Term Σ₁ Γ) (empty-ctx (Ty Σ₀))
    the-subst x = ⊥.rec (¬Fin0 x)

    the-only-subst : ∀ {Γ} → (γ : substitution (Term Σ₁ Γ) (empty-ctx (Ty Σ₀))) → the-subst ≡ γ
    the-only-subst γ = funExt (λ x → rec (¬Fin0 x))
    
  completeness ._,,_ = {!!}
  completeness .Ob = Ty Σ₀
  completeness .Tm = Tm-presheaf
  completeness .Tm-repr A = UniversalElementToRepresentation STTCtx (Tm-presheaf A) (((sole A) , (var (the-var A))) , the-var-is-terminal)
    where

      the-var-is-terminal : isTerminal (Contravariant.∫ᴾ_ {C = STTCtx} (Tm-presheaf A)) (sole A , var (the-var A))
      the-var-is-terminal (Γ , M) =
          ((λ x → M) , refl) , λ M/x' → Σ≡Prop {!!} (funExt (λ x → M ≡⟨ M/x' .snd ⟩ (M/x' .fst (the-var A)) ≡⟨ (λ i → M/x' .fst (isContr→isProp isContrFin1 (the-var A) x i)) ⟩ M/x' .fst x ∎))
