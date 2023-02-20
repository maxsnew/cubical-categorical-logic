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

-- Three levels are for:
--  ℓo: type of contexts/objects
--  ℓt: type of substitutions/terms
record SimplyTypedCategory (ℓo ℓt : Level) : Type ((ℓ-max (ℓ-suc ℓo) (ℓ-suc ℓt))) where
  open Category
  field
    -- A cartesian category B of contexts and substitutions
    B    : Category ℓo ℓt
    ·    : Terminal B
    _,,_ : BinProducts B
    -- a type of objects and for each object a presheaf of terms for that object
    Ob   : Type ℓo
    Tm   : ∀ (A : Ob) → Presheaf B ℓt
    -- Tm A is always representable, this defines a context containing a single variable
    Tm-repr : ∀ (A : Ob) → Representation B (Tm A)

open SimplyTypedCategory
open Category
open Functor
open NatTrans

presheaf-⊤ : ∀ {ℓo ℓt} ℓS (C : Category ℓo ℓt) → Presheaf C ℓS
presheaf-⊤ ℓS C .F-ob Γ = Unit* , isSetUnit*
presheaf-⊤ ℓS C .F-hom = λ x₁ x₂ → tt*
presheaf-⊤ ℓS C .F-id = refl
presheaf-⊤ ℓS C .F-seq = λ f g → refl

presheaf-× : ∀ {ℓo ℓt ℓS} (C : Category ℓo ℓt) → (P Q : Presheaf C ℓS) → Presheaf C ℓS
presheaf-× C P Q .F-ob  = λ a → ((fst (P ⟅ a ⟆)) × (fst (Q ⟅ a ⟆))) , isSet× (snd (P ⟅ a ⟆ )) (snd (Q ⟅ a ⟆))
presheaf-× C P Q .F-hom f (ϕ₁ , ϕ₂) = C [ ϕ₁ ∘ᴾ⟨ P ⟩ f ] , C [ ϕ₂ ∘ᴾ⟨ Q ⟩ f ]
presheaf-× C P Q .F-id  = funExt λ ϕ i → (∘ᴾId C P (fst ϕ) i) , ((∘ᴾId C Q (snd ϕ) i))
presheaf-× C P Q .F-seq f g = funExt (λ ϕ i → (∘ᴾAssoc C P (fst ϕ) f g i) , ((∘ᴾAssoc C Q (snd ϕ) f g i) ))

presheaf-Prod : ∀ {ℓo ℓt ℓS} (C : Category ℓo ℓt)
              → (J : Type ℓS)
              → (J → Presheaf C ℓS)
              → Presheaf C ℓS
presheaf-Prod C J Ps .F-ob Γ = ((j : J) → fst (Ps j ⟅ Γ ⟆) ) , isSetΠ (λ j → snd (Ps j ⟅ Γ ⟆))
presheaf-Prod C J Ps .F-hom = λ γ ϕs j → C [ ϕs j ∘ᴾ⟨ Ps j ⟩ γ ]
presheaf-Prod C J Ps .F-id = funExt (λ ϕs i j → ∘ᴾId C (Ps j) (ϕs j) i)
presheaf-Prod C J Ps .F-seq δ γ = λ i ϕs j → ∘ᴾAssoc C (Ps j) (ϕs j) δ γ i

-- A presheaf P on the base category is representable as a type when
-- there is an object of the STC whose presheaf of terms is equivelent
-- to P
TypeRepresentation : ∀ {ℓo ℓt} (C : SimplyTypedCategory ℓo ℓt) → (P : Presheaf (C .B) ℓt) → Type (ℓ-max ℓo ℓt)
TypeRepresentation C P = Σ[ A ∈ C .Ob ] CatIso (PresheafCategory (C .B) _) (C .Tm A) P

AllProductTypes : ∀ {ℓo ℓt} → SimplyTypedCategory ℓo ℓt → Type (ℓ-max ℓo (ℓ-suc ℓt))
AllProductTypes {ℓo}{ℓt} C =
  ∀ (J : Type ℓt) (D : J → C .Ob)
  → TypeRepresentation C (presheaf-Prod (C .B) J (λ j → C .Tm (D j)))

FinProductTypes : ∀ {ℓo ℓt} → SimplyTypedCategory ℓo ℓt → Type (ℓ-max ℓo (ℓ-suc ℓt))
FinProductTypes {ℓo}{ℓt} C =
  ∀ (J : Type ℓt) (D : J → C .Ob)
  → TypeRepresentation C (presheaf-Prod (C .B) J (λ j → C .Tm (D j)))

record STC-Functor {ℓo ℓt} (C D : SimplyTypedCategory ℓo ℓt) : Type (ℓ-max ℓo ℓt) where
  field
    B-functor : Functor (C .B) (D .B)
    -- TODO: preserves products
    Ob-fun : C .Ob → D .Ob
    Tm-fun : ∀ A → (PresheafCategory (C .B) ℓt) [ C .Tm A , (D .Tm (Ob-fun A) ∘F (B-functor ^opF)) ]
    -- TODO: preserves Tm-representability
