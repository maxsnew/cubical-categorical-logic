module NaturalModels.Cartesian where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import UMP

open Category
open CartesianCategory
open UnivElt
open isUniversal

record SimplyTypedCategory (ℓb ℓb' ℓt ℓt' : Level) : Type (ℓ-suc (ℓ-max ℓb (ℓ-max ℓb' (ℓ-max ℓt ℓt')))) where
  field
    -- A cartesian category B of contexts and substitutions
    B    : CartesianCategory ℓb ℓb'
    -- a type of objects and for each object a presheaf of terms for that object
    Ty   : Type ℓt
    Tm   : ∀ (A : Ty) → Presheaf (B .cat) ℓt'
    -- Tm A is always representable, this defines a context containing a single variable
    Tm-repr : ∀ (A : Ty) → UnivElt (B .cat) (Tm A)

  sole : ∀ (A : Ty) → B .cat .ob
  sole A = Tm-repr A .vertex

  the-var : ∀ {A} → (Tm A ⟅ sole A ⟆) .fst
  the-var = Tm-repr _ .element

  _/the-var : ∀ {Γ A} → (Tm A ⟅ Γ ⟆) .fst → B .cat [ Γ , sole A ]
  _/the-var M = Tm-repr _ .universal .coinduction M

  _⟨_⟩S : ∀ {Δ Γ A} → (Tm A ⟅ Γ ⟆) .fst → B .cat [ Δ , Γ ] → (Tm A ⟅ Δ ⟆) .fst
  M ⟨ γ ⟩S = B .cat [ M ∘ᴾ⟨ Tm _ ⟩ γ ]

  ⟨/the-var⟩ : ∀ {Γ A} (M : (Tm A ⟅ Γ ⟆) .fst)
             → the-var ⟨ M /the-var ⟩S ≡ M
  ⟨/the-var⟩ = Tm-repr _ .universal .commutes

  /the-var⟨⟩S : ∀ {Δ Γ A} (M : (Tm A ⟅ Γ ⟆) .fst) (γ : B .cat [ Δ , Γ ])
              → (M /the-var) ∘⟨ B .cat ⟩ γ ≡ (M ⟨ γ ⟩S) /the-var
  /the-var⟨⟩S M γ = Tm-repr _ .universal .is-uniq (M ⟨ γ ⟩S) ((M /the-var) ∘⟨ B .cat ⟩ γ)
    (the-var ⟨ M /the-var ∘⟨ B .cat ⟩ γ ⟩S
      ≡⟨ ∘ᴾAssoc (B .cat) (Tm _) _ _ _ ⟩
    the-var ⟨ M /the-var ⟩S ⟨ γ ⟩S
      ≡[ i ]⟨ ⟨/the-var⟩ M i ⟨ γ ⟩S ⟩
    M ⟨ γ ⟩S ∎)

open SimplyTypedCategory
open Functor
open NatTrans

record STC-Functor {ℓcb ℓcb' ℓct ℓct' ℓdb ℓdb' ℓdt ℓdt'}
       (C : SimplyTypedCategory ℓcb ℓcb' ℓct ℓct')
       (D : SimplyTypedCategory ℓdb ℓdb' ℓdt ℓdt') :
       Type (ℓ-max ℓcb (ℓ-max ℓcb' (ℓ-max ℓct (ℓ-max ℓct' (ℓ-max ℓdb (ℓ-max ℓdb' (ℓ-max ℓdt (ℓ-max ℓdt' (ℓ-suc ℓ-zero))))))))) where
  open CartesianFunctor
  field
    F-B : CartesianFunctor (C .B) (D .B)
    F-Ty : C .Ty → D .Ty
    F-Tm : ∀ A → PshHom (F-B .func) (C .Tm A) (D .Tm (F-Ty A))
    F-Tm-repr : ∀ A → preserves-representation (F-B .func) (C .Tm A) (D .Tm (F-Ty A)) (F-Tm A) (C .Tm-repr A)

-- | Universal Properties
private
  variable
    ℓb ℓb' ℓt ℓt' ℓp : Level

-- A presheaf P on the base category is representable as a type when
-- there is an object of the STC whose presheaf of terms is equivelent
-- to P
TypeRepresentation : ∀ (C : SimplyTypedCategory ℓb ℓb' ℓt ℓt') → (P : Presheaf (C .B .cat) ℓp) → Type _
TypeRepresentation C P = Σ[ A ∈ C .Ty ] PshIso (C .B .cat) (C .Tm A) P

-- AllProductTypes : ∀ {ℓo ℓt} → SimplyTypedCategory ℓo ℓt → Type (ℓ-max ℓo (ℓ-suc ℓt))
-- AllProductTypes {ℓo}{ℓt} C =
--   ∀ (J : Type ℓt) (D : J → C .Ty)
--   → TypeRepresentation C (presheaf-Prod (C .B .cat) J (λ j → C .Tm (D j)))

-- FinProductTypes : ∀ {ℓo ℓt} → SimplyTypedCategory ℓo ℓt → Type (ℓ-max ℓo (ℓ-suc ℓt))
-- FinProductTypes {ℓo}{ℓt} C =
--   ∀ (J : Type ℓt) (D : J → C .Ty)
--   → TypeRepresentation C (presheaf-Prod (C .B .cat) J (λ j → C .Tm (D j)))

-- | TODO: Exponentials as representing the exponential of presheaves
-- | or the more syntactic-looking Tm (a => b) G =~ Tm b (G x sole A)

-- | TODO: coproducts are "just" coproducts in the category of terms
-- | with a free variable.
