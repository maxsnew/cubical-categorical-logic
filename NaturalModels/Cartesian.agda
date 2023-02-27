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

  _/var : ∀ {Γ A} → (Tm A ⟅ Γ ⟆) .fst → B .cat [ Γ , sole A ]
  M /var = Tm-repr _ .universal .coinduction M

open SimplyTypedCategory
open Functor
open NatTrans

record STC-Functor {ℓcb ℓcb' ℓct ℓct' ℓdb ℓdb' ℓdt ℓdt'}
       (C : SimplyTypedCategory ℓcb ℓcb' ℓct ℓct')
       (D : SimplyTypedCategory ℓdb ℓdb' ℓdt ℓdt') :
       Type (ℓ-max ℓcb (ℓ-max ℓcb' (ℓ-max ℓct (ℓ-max ℓct' (ℓ-max ℓdb (ℓ-max ℓdb' (ℓ-max ℓdt ℓdt'))))))) where
  open CartesianFunctor
  field
    F-B : CartesianFunctor (C .B) (D .B)
    F-Ty : C .Ty → D .Ty
    F-Tm : ∀ A → PshHom (F-B .func) (C .Tm A) (D .Tm (F-Ty A))
    F-Tm-repr : ∀ A → preserves-representability (F-B .func) (C .Tm A) (D .Tm (F-Ty A)) (F-Tm A)

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
