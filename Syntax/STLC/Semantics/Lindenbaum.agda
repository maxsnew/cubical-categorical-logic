module Syntax.STLC.Semantics.Lindenbaum where

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Constructions.Elements
open import Cubical.Categories.Limits.Terminal
open import Cubical.Data.Sigma
open import Cubical.Data.Fin
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels

open import Syntax.STLC renaming (Tm to Term)
open import NaturalModels.Cartesian
open import NamedContext
open import UMP

open Functor

module _ {ℓ}{Σ₀ : Sig₀ ℓ}{Σ₁ : Sig₁ Σ₀} where
  open Category
  open SimplyTypedCategory

  STTCtx : Category (ℓ-max ℓ (ℓ-suc ℓ-zero)) ℓ
  STTCtx .ob = Ctx (Ty Σ₀)
  STTCtx .Hom[_,_] Δ Γ = substitution (Term Σ₁ Δ) Γ -- substitution (Term Σ₁ Δ) Γ
  STTCtx .id {Γ} = id-subst Γ
  STTCtx ._⋆_ {z = Γ} = λ δ γ → comp-subst {Γ = Γ} γ δ -- comp-subst γ δ
  STTCtx .⋆IdL {y = Γ} = comp-subst-IdInp {Γ = Γ}
  STTCtx .⋆IdR {y = Γ} = comp-subst-IdOutp {Γ = Γ}
  STTCtx .⋆Assoc {w = Γ} = λ f g h → comp-subst-Assoc {Γ = Γ} h g f
  STTCtx .isSetHom {y = Γ} = isSetTTProof.isSetSubst Σ₀ Σ₁ _ Γ

  Tm-presheaf : ∀ A → Presheaf STTCtx ℓ
  Tm-presheaf A .F-ob Γ = (Term Σ₁ Γ A) , isSetTTProof.isSetTm Σ₀ Σ₁ Γ A
  Tm-presheaf A .F-hom = λ γ M → M ⟨ γ ⟩
  Tm-presheaf A .F-id = funExt subst-idInp
  Tm-presheaf A .F-seq γ δ = funExt λ M → subst-Assoc M γ δ

  Tm-univElt : ∀ A → UniversalElement STTCtx (Tm-presheaf A)
  Tm-univElt A = (singleton A , ivar tt) , is-universal where
    is-universal : isTerminal (Contravariant.∫ᴾ_ {C = STTCtx} (Tm-presheaf A)) (singleton A , ivar tt)
    is-universal (Γ , M) = ((λ x → M) , refl) , is-uniq where
      is-uniq : (alt : (Contravariant.∫ᴾ_ {C = STTCtx} (Tm-presheaf A)) [ (Γ , M) , (singleton A , ivar tt) ]) → ((λ x → M) , (λ _ → M)) ≡ alt
      is-uniq (σ , M≡σ*) = Σ≡Prop (λ x → snd (Tm-presheaf A ⟅ Γ ⟆) M _) (funExt (λ x → M≡σ*))

  open BinProduct
  open Ctx
  open CartesianCategory

  -- the "Lindenbaum algebra" of terms/Syntactic category
  Lindenbaum : SimplyTypedCategory (ℓ-max ℓ (ℓ-suc ℓ-zero)) ℓ ℓ ℓ
  Lindenbaum .B .cat = STTCtx
  Lindenbaum .B .terminal-ob .fst .fst = empty-ctx
  Lindenbaum .B .terminal-ob .fst .snd = tt
  Lindenbaum .B .terminal-ob .snd (Γ , _) .fst .fst = λ ()
  Lindenbaum .B .terminal-ob .snd (Γ , _) .fst .snd = refl
  Lindenbaum .B .terminal-ob .snd (Γ , _) .snd (!' , _) =
    Σ≡Prop (λ x → isSetUnit tt tt) (funExt (λ ()))
  Lindenbaum .B .product-ob Γ₁ Γ₂ .fst .fst = append Γ₁ Γ₂
  Lindenbaum .B .product-ob Γ₁ Γ₂ .fst .snd = (λ x → ivar (inl x)) , (λ x → ivar (inr x))
  Lindenbaum .B .product-ob Γ₁ Γ₂ .snd (Γ , γ₁ , γ₂) .fst .fst (inl x) = γ₁ x
  Lindenbaum .B .product-ob Γ₁ Γ₂ .snd (Γ , γ₁ , γ₂) .fst .fst (inr x) = γ₂ x
  Lindenbaum .B .product-ob Γ₁ Γ₂ .snd (Γ , γ₁ , γ₂) .fst .snd = refl
  Lindenbaum .B .product-ob Γ₁ Γ₂ .snd (Γ , γ₁ , γ₂) .snd (γ , γ₁γ₂≡) =
    Σ≡Prop ((λ γ → isSet× (isSetTTProof.isSetSubst _ _ _ Γ₁)
                          (isSetTTProof.isSetSubst _ _ _ Γ₂)
                          _ _))
           (funExt pf) where
      pf : (x : Γ₁ .var ⊎ Γ₂ .var) → Lindenbaum .B .product-ob Γ₁ Γ₂ .snd (Γ , γ₁ , γ₂) .fst .fst x ≡ γ x
      pf (inl x) = λ i → γ₁γ₂≡ i .fst x
      pf (inr x) = λ i → γ₁γ₂≡ i .snd x
  Lindenbaum .Ob = (Ty Σ₀)
  Lindenbaum .Tm = Tm-presheaf
  Lindenbaum .Tm-repr = Tm-univElt
