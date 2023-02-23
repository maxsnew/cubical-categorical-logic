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

record SimplyTypedCategory (ℓb ℓb' ℓt ℓt' : Level) : Type (ℓ-suc (ℓ-max ℓb (ℓ-max ℓb' (ℓ-max ℓt ℓt')))) where
  field
    -- A cartesian category B of contexts and substitutions
    B    : CartesianCategory ℓb ℓb'
    -- a type of objects and for each object a presheaf of terms for that object
    Ob   : Type ℓt
    Tm   : ∀ (A : Ob) → Presheaf (B .cat) ℓt'
    -- Tm A is always representable, this defines a context containing a single variable
    Tm-repr : ∀ (A : Ob) → UniversalElement (B .cat) (Tm A)

open SimplyTypedCategory
open Functor
open NatTrans

-- A presheaf P on the base category is representable as a type when
-- there is an object of the STC whose presheaf of terms is equivelent
-- to P
-- TypeRepresentation : ∀ {ℓo ℓt} (C : SimplyTypedCategory ℓo ℓt) → (P : Presheaf (C .B .cat) ℓt) → Type (ℓ-max ℓo ℓt)
-- TypeRepresentation C P = Σ[ A ∈ C .Ob ] CatIso (PresheafCategory (C .B .cat) _) (C .Tm A) P

-- AllProductTypes : ∀ {ℓo ℓt} → SimplyTypedCategory ℓo ℓt → Type (ℓ-max ℓo (ℓ-suc ℓt))
-- AllProductTypes {ℓo}{ℓt} C =
--   ∀ (J : Type ℓt) (D : J → C .Ob)
--   → TypeRepresentation C (presheaf-Prod (C .B .cat) J (λ j → C .Tm (D j)))

-- FinProductTypes : ∀ {ℓo ℓt} → SimplyTypedCategory ℓo ℓt → Type (ℓ-max ℓo (ℓ-suc ℓt))
-- FinProductTypes {ℓo}{ℓt} C =
--   ∀ (J : Type ℓt) (D : J → C .Ob)
--   → TypeRepresentation C (presheaf-Prod (C .B .cat) J (λ j → C .Tm (D j)))

record STC-Functor {ℓcb ℓcb' ℓct ℓct' ℓdb ℓdb' ℓdt ℓdt'}
       (C : SimplyTypedCategory ℓcb ℓcb' ℓct ℓct')
       (D : SimplyTypedCategory ℓdb ℓdb' ℓdt ℓdt') :
       Type (ℓ-max ℓcb (ℓ-max ℓcb' (ℓ-max ℓct (ℓ-max ℓct' (ℓ-max ℓdb (ℓ-max ℓdb' (ℓ-max ℓdt ℓdt'))))))) where
  open CartesianFunctor
  field
    F-B : CartesianFunctor (C .B) (D .B)
    F-Ob : C .Ob → D .Ob
    F-Tm : ∀ A → PshHom (F-B .func) (C .Tm A) (D .Tm (F-Ob A))
    F-Tm-repr : ∀ A → preserves-representability (F-B .func) (C .Tm A) (D .Tm (F-Ob A)) (F-Tm A)
