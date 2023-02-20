module Syntax.STLC.Semantics where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Limits.BinProduct
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
  STTCtx .ob = Ctx (Ty Σ₀)
  STTCtx .Hom[_,_] Δ Γ = substitution (Term Σ₁ Δ) Γ -- substitution (Term Σ₁ Δ) Γ
  STTCtx .id {Γ} = id-subst Γ
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

  Tm-univElt : ∀ A → UniversalElement STTCtx (Tm-presheaf A)
  Tm-univElt A = ((sole A) , (var (the-var A))) , is-universal where
    is-universal : isTerminal (Contravariant.∫ᴾ_ {C = STTCtx} (Tm-presheaf A)) (sole A , var (the-var A))
    is-universal (Γ , M) = ((λ x → M) , refl) , is-uniq where
      is-uniq : (alt : (Contravariant.∫ᴾ_ {C = STTCtx} (Tm-presheaf A)) [ (Γ , M) , (sole A , var (the-var A)) ]) → ((λ x → M) , (λ _ → M)) ≡ alt
      is-uniq (σ , M≡σ*) = Σ≡Prop (λ x → snd (Tm-presheaf A ⟅ Γ ⟆) M _) (funExt lem) where
        lem : ∀ (x : Var (sole A)) → M ≡ σ x
        lem x =
          M             ≡⟨ M≡σ* ⟩
          σ (the-var A) ≡⟨ cong σ (isContr→isProp isContrFin1 (the-var A) x) ⟩
          σ x ∎

  open BinProduct
  completeness : SimplyTypedCategory ℓ ℓ
  completeness .B = STTCtx
  completeness .· = empty-ctx _ , λ Γ → !-subst Γ , !-subst-uniq Γ where
    !-subst : ∀ Γ → STTCtx [ Γ , empty-ctx _ ]
    !-subst Γ = λ x → rec (¬Fin0 x)

    !-subst-uniq : ∀ Γ (!' : STTCtx [ Γ , empty-ctx (Ty Σ₀) ]) → !-subst Γ ≡ !'
    !-subst-uniq Γ !' = funExt (λ x → rec (¬Fin0 x))
  completeness ._,,_ Γ₁ Γ₂ .binProdOb  = append-ctx Γ₁ Γ₂
  completeness ._,,_ Γ₁ Γ₂ .binProdPr₁ = λ x₁ → transport (cong (Term Σ₁ (append-ctx Γ₁ Γ₂)) (append-i₁-elts Γ₁ Γ₂ x₁)) (var (append-i₁ Γ₁ Γ₂ x₁))
  completeness ._,,_ Γ₁ Γ₂ .binProdPr₂ = λ x₂ → transport (cong (Term Σ₁ (append-ctx Γ₁ Γ₂)) (append-i₂-elts Γ₁ Γ₂ x₂)) (var (append-i₂ Γ₁ Γ₂ x₂))
  completeness ._,,_ Γ₁ Γ₂ .univProp {z = Γ} γ₁ γ₂ =
    ((append-subst {B = Term Σ₁ Γ} γ₁ γ₂) , {!!} , {!!}) , {!!}
  completeness .Ob = Ty Σ₀ -- Ty Σ₀
  completeness .Tm = Tm-presheaf
  completeness .Tm-repr A = {!!} -- UniversalElementToRepresentation STTCtx (Tm-presheaf A) (Tm-univElt A)
    
