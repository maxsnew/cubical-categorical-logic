{- Algebras of a monad formulated in terms of extension systems -}
module Cubical.Categories.Monad.Algebra where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor renaming (𝟙⟨_⟩ to funcId)
open import Cubical.Categories.Monad.ExtensionSystem
open import Cubical.Categories.Adjoint.UniversalElements

private
  variable
    ℓ ℓ' : Level

module _ {C : Category ℓ ℓ'} (M : ExtensionSystem C) where
  open Category
  T = M .fst
  open ExtensionSystemFor (M .snd)

  record AlgebraFor (a : C .ob) : Type (ℓ-max ℓ ℓ') where
    field
      bindA : ∀ {b} → C [ b , a ] → C [ T b , a ]
      bindA-l : ∀ {b}{f : C [ b , a ]} → bindA f ∘⟨ C ⟩ η ≡ f
      bindA-comp : ∀ {b c} {f : C [ b , a ]}{g : C [ c , T b ]}
        → bindA f ∘⟨ C ⟩ bind g ≡ bindA (bindA f ∘⟨ C ⟩ g)

  open AlgebraFor

  isAlgebraHom : ∀ {a b} → AlgebraFor a → AlgebraFor b → (C [ a , b ]) → Type _
  isAlgebraHom α β ϕ =
    ∀ {c} (f : C [ c , _ ]) → ϕ ∘⟨ C ⟩ α .bindA f ≡ β .bindA (ϕ ∘⟨ C ⟩ f)

  isPropIsAlgebraHom : ∀ {a b} →
                       (α : AlgebraFor a)(β : AlgebraFor b)
                       (ϕ : C [ a , b ]) → isProp (isAlgebraHom α β ϕ)
  isPropIsAlgebraHom α β ϕ =
    isPropImplicitΠ λ _ → isPropΠ λ f → C .isSetHom _ _

  Algebra = Σ[ a ∈ C .ob ] AlgebraFor a

  AlgebraHom : Algebra → Algebra → Type _
  AlgebraHom α β =
    Σ[ ϕ ∈ C [ α .fst , β .fst ] ] isAlgebraHom (α .snd) (β .snd) ϕ

  isSetAlgebraHom : ∀ {α β} → isSet (AlgebraHom α β)
  isSetAlgebraHom {x}{y} =
    isSetΣ (C .isSetHom)
      (λ ϕ → isProp→isSet (isPropIsAlgebraHom (x .snd) (y .snd) ϕ))

  AlgebraHom≡ : ∀ {α β} (ϕ ψ : AlgebraHom α β) → ϕ .fst ≡ ψ .fst → ϕ ≡ ψ
  AlgebraHom≡ {α}{β} ϕ ψ p =
    Σ≡Prop (λ ϕ → isPropIsAlgebraHom (α .snd) (β .snd) ϕ) p

  ALGEBRA : Category _ _
  ALGEBRA .ob = Algebra
  ALGEBRA .Hom[_,_] = AlgebraHom
  ALGEBRA .id {x} =
    C .id , λ f → (C .⋆IdR _) ∙ cong (x .snd .bindA) (sym (C .⋆IdR _))
  ALGEBRA ._⋆_ {z = γ} ϕ ψ =
    (ϕ .fst ⋆⟨ C ⟩ ψ .fst) , (λ f →
    sym (C .⋆Assoc _ _ _) ∙
      cong₂ (C ._⋆_) (ϕ .snd _) refl ∙ ψ .snd _ ∙
        cong (γ .snd .bindA) (C .⋆Assoc _ _ _))
  ALGEBRA .⋆IdL {x}{y} ϕ =
    Σ≡Prop (isPropIsAlgebraHom (x .snd) (y .snd)) (C .⋆IdL _)
  ALGEBRA .⋆IdR {x}{y} ϕ =
    Σ≡Prop (isPropIsAlgebraHom (x .snd) (y .snd)) (C .⋆IdR _)
  ALGEBRA .⋆Assoc {w}{x}{y}{z} f g h =
    Σ≡Prop (isPropIsAlgebraHom (w .snd) (z .snd)) (C .⋆Assoc _ _ _)
  ALGEBRA .isSetHom {x}{y} =
    isSetΣ (C .isSetHom)
      (λ ϕ → isProp→isSet (isPropIsAlgebraHom (x .snd) (y .snd) ϕ))

  open Functor

  FreeAlgebra : ∀ (a : C .ob) → Algebra
  FreeAlgebra a = T a , free-alg where
    free-alg : AlgebraFor (T a)
    free-alg .bindA = bind
    free-alg .bindA-l = bind-l
    free-alg .bindA-comp = bind-comp

  funToFreeHom : ∀ (a b : C .ob) →
                 (Kleisli _ M [ a , b ]) →
                 AlgebraHom (FreeAlgebra a) (FreeAlgebra b)
  funToFreeHom a b f .fst = bind f
  funToFreeHom a b f .snd g = bind-comp

  Underlying : Functor ALGEBRA C
  Underlying .F-ob x = x .fst
  Underlying .F-hom x = x .fst
  Underlying .F-id = refl
  Underlying .F-seq f g = refl

  open import Cubical.Categories.Presheaf.Representable
  open UniversalElement
  open isEquiv
  Free : LeftAdjoint Underlying
  Free c .vertex = FreeAlgebra c
  Free c .element = η
  Free c .universal β = isIsoToIsEquiv
    ( (λ f → β .snd .bindA f , λ _ → β .snd .bindA-comp)
    , (λ f → β .snd .bindA-l)
    , λ ϕ → AlgebraHom≡ {FreeAlgebra _}{β} _ _
      ( sym (ϕ .snd η)
      ∙ cong (comp' C _) bind-r
      ∙ C .⋆IdL _))
