{-# OPTIONS --safe #-}
module Cubical.Categories.Constructions.Power where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Functor

private
  variable
    ℓ ℓc ℓc' : Level

open Category

PowerCategory : (X : Type ℓ) (C : Category ℓc ℓc') → Category _ _
PowerCategory X C .ob = X → C .ob
PowerCategory X C .Hom[_,_] f g = (x : X) → C [ f x , g x ]
PowerCategory X C .id = λ x → id C
PowerCategory X C ._⋆_ = λ f g x → (f x) ⋆⟨ C ⟩ (g x)
PowerCategory X C .⋆IdL f = funExt (λ x → ⋆IdL C (f x))
PowerCategory X C .⋆IdR f = funExt λ x → ⋆IdR C (f x)
PowerCategory X C .⋆Assoc f g h = funExt λ x → ⋆Assoc C (f x) (g x) (h x)
PowerCategory X C .isSetHom = isSetΠ λ x → isSetHom C

PseudoYoneda : {C : Category ℓc ℓc'} → Functor C (PowerCategory (C .ob) (SET ℓc'))
PseudoYoneda {C = C} .Functor.F-ob x y = (C [ y , x ]) , isSetHom C
PseudoYoneda {C = C} .Functor.F-hom f z = comp' C f
PseudoYoneda {C = C} .Functor.F-id = funExt (λ Γ → funExt λ x' → ⋆IdR C x')
PseudoYoneda {C = C} .Functor.F-seq f g = funExt (λ x → funExt λ x' → sym (C .⋆Assoc x' f g))

isFaithfulPseudoYoneda : {C : Category ℓc ℓc'} → Functor.isFaithful (PseudoYoneda {C = C})
isFaithfulPseudoYoneda {C = C} x y f g p = sym (C .⋆IdL f) ∙ (λ i → p i _ (C .id)) ∙ C .⋆IdL g

-- TODO: if the base category is univalent then so is the power category?

-- Just to demonstrate that if the base category is strict then the power category is strict
PowerCategoryS : (X : Type ℓ) → (ℓ' : Level) → Category _ _
PowerCategoryS X ℓ' .ob = X → hSet ℓ'
PowerCategoryS X ℓ' .Hom[_,_] As Bs = (x : X) → ⟨ As x ⟩ → ⟨ Bs x ⟩
PowerCategoryS X ℓ' .id = λ x z → z
PowerCategoryS X ℓ' ._⋆_ = λ f g x z → g x (f x z)
PowerCategoryS X ℓ' .⋆IdL f = refl
PowerCategoryS X ℓ' .⋆IdR f = refl
PowerCategoryS X ℓ' .⋆Assoc f g h = refl
PowerCategoryS X ℓ' .isSetHom {y = Bs} = isSetΠ λ x → isSetΠ λ y → str (Bs x)

PseudoYonedaS : {C : Category ℓc ℓc'} → Functor C (PowerCategoryS (C .ob) ℓc')
PseudoYonedaS {C = C} .Functor.F-ob x y = (C [ y , x ]) , isSetHom C
PseudoYonedaS {C = C} .Functor.F-hom f z = comp' C f
PseudoYonedaS {C = C} .Functor.F-id = funExt (λ Γ → funExt λ x' → ⋆IdR C x')
PseudoYonedaS {C = C} .Functor.F-seq f g = funExt (λ x → funExt λ x' → sym (C .⋆Assoc x' f g))

isFaithfulPseudoYonedaS : {C : Category ℓc ℓc'} → Functor.isFaithful (PseudoYonedaS {C = C})
isFaithfulPseudoYonedaS {C = C} x y f g p = sym (C .⋆IdL f) ∙ (λ i → p i _ (C .id)) ∙ C .⋆IdL g
