
module Cubical.Categories.Functors.More where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Isomorphism.More
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functor.Compose
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Functions.Embedding
open import Cubical.HITs.PropositionalTruncation as Prop

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level
    C : Category ℓC ℓC'
    D : Category ℓD ℓD'
    E : Category ℓE ℓE'

open Category
open Functor
open NatTrans

ConstantComposeFunctor :
  (C : Category ℓC ℓC') (D : Category ℓD ℓD' ) (c : C .ob)
  (F : Functor C D) →
  Constant (D ^op) D (F .F-ob c) ≡ F ∘F Constant (D ^op) C c
ConstantComposeFunctor C D c F = Functor≡
  (λ c → ( refl ))
    (λ f → (
      D .id
     ≡⟨ sym (F .F-id) ⟩
       F ⟪ Constant (D ^op) C c ⟪ f ⟫ ⟫ ∎
  ))

-- The data of a functor, parameterized by the action on objects
record ActionOnMorphisms
  (C : Category ℓC ℓC')
  (D : Category ℓD ℓD')
  (F₀ : C .ob → D .ob) : Type (ℓ-max (ℓ-max ℓC ℓC') ℓD') where
  no-eta-equality

  open Category

  field
    F-hom : {x y : C .ob} → C [ x , y ] → D [ F₀ x , F₀ y ]
    F-id  : {x : C .ob} → F-hom (C .id) ≡ D .id {x = F₀ x}
    F-seq : {x y z : C .ob} (f : C [ x , y ]) (g : C [ y , z ])
          → F-hom (f ⋆⟨ C ⟩ g) ≡ (F-hom f) ⋆⟨ D ⟩ (F-hom g)

open ActionOnMorphisms

ActionOnMorphisms→Functor :
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}{F₀ : C .ob → D .ob}
                          → ActionOnMorphisms C D F₀
                          → Functor C D
ActionOnMorphisms→Functor {F₀ = F₀} F₁ .F-ob = F₀
ActionOnMorphisms→Functor {F₀ = F₀} F₁ .F-hom = F₁ .F-hom
ActionOnMorphisms→Functor {F₀ = F₀} F₁ .F-id = F₁ .F-id
ActionOnMorphisms→Functor {F₀ = F₀} F₁ .F-seq = F₁ .F-seq


module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         (F : Functor C D)
         where
  open NatTrans
  open NatIso
  open isIso
  hasIsoRetraction→isFaithful : (F⁻ : Functor D C) (ret : F⁻ ∘F F ≅ᶜ Id)
    → isFaithful F
  hasIsoRetraction→isFaithful F⁻ ret x y f g F⟪f⟫≡F⟪g⟫ =
    ⋆CancelL (NatIsoAt ret _)
      (sym (ret .trans .N-hom f)
      ∙ cong₂ (seq' C) (cong (F⁻ .F-hom) F⟪f⟫≡F⟪g⟫) refl
      ∙ ret .trans .N-hom g)
