module UMP where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Instances.Sets
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Data.FinSet
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open Category
open Functor
open NatTrans
open UnivElt

private
  variable
    ℓc ℓc' ℓd ℓd' ℓp ℓj : Level

⊤ᴾ : ∀ {ℓo ℓt} (C : Category ℓo ℓt) → Presheaf C ℓ-zero
⊤ᴾ C .F-ob Γ = Unit , isSetUnit
⊤ᴾ C .F-hom = λ x₁ x₂ → tt
⊤ᴾ C .F-id = refl
⊤ᴾ C .F-seq = λ f g → refl

push-⊤ᴾ : {C : Category ℓc ℓc'} {D : Category ℓd ℓd'} (F : Functor C D) → PshHom F (⊤ᴾ C) (⊤ᴾ D)
push-⊤ᴾ F .N-ob _ _ = lift tt
push-⊤ᴾ F .N-hom f = funExt (λ _ → refl)

preserves-⊤ : {C : Category ℓc ℓc'} {D : Category ℓd ℓd'} (F : Functor C D) → Type (ℓ-max (ℓ-max (ℓ-max ℓc ℓc') ℓd) ℓd')
preserves-⊤ {C = C}{D} F =
  preserves-representability F (⊤ᴾ C) (⊤ᴾ D) (push-⊤ᴾ F)

×ᴾ : ∀ {ℓo ℓt ℓS} (C : Category ℓo ℓt) → (P Q : Presheaf C ℓS) → Presheaf C ℓS
×ᴾ C P Q .F-ob  = λ a → ((fst (P ⟅ a ⟆)) × (fst (Q ⟅ a ⟆))) , isSet× (snd (P ⟅ a ⟆ )) (snd (Q ⟅ a ⟆))
×ᴾ C P Q .F-hom f (ϕ₁ , ϕ₂) = C [ ϕ₁ ∘ᴾ⟨ P ⟩ f ] , C [ ϕ₂ ∘ᴾ⟨ Q ⟩ f ]
×ᴾ C P Q .F-id  = funExt λ ϕ i → (∘ᴾId C P (fst ϕ) i) , ((∘ᴾId C Q (snd ϕ) i))
×ᴾ C P Q .F-seq f g = funExt (λ ϕ i → (∘ᴾAssoc C P (fst ϕ) f g i) , ((∘ᴾAssoc C Q (snd ϕ) f g i) ))

-- TODO: should be easier using limit formulation
push-×ᴾ : {C : Category ℓc ℓc'} {D : Category ℓd ℓd'} (F : Functor C D) (a b : C .ob)
        → PshHom F (×ᴾ C (C [-, a ]) (C [-, b ])) (×ᴾ D (D [-, F ⟅ a ⟆ ]) (D [-, F ⟅ b ⟆ ]))
push-×ᴾ F a b .N-ob c (lift (f₁ , f₂)) = lift ((F .F-hom f₁) , (F .F-hom f₂))
push-×ᴾ {C = C}{D} F a b .N-hom f = funExt λ (lift (f₁ , f₂)) →
  λ i → lift ((F .F-seq f f₁ i) , ((F .F-seq f f₂ i)))

preserves-× : {C : Category ℓc ℓc'} {D : Category ℓd ℓd'} (F : Functor C D) → Type _
preserves-× {C = C}{D} F = (a b : C .ob) →
  preserves-representability F (×ᴾ C (C [-, a ]) (C [-, b ]))
                               (×ᴾ D (D [-, F ⟅ a ⟆ ]) (D [-, F ⟅ b ⟆ ]))
                               (push-×ᴾ F a b)


Πfinᴾ : ∀ {ℓo ℓt ℓS} (C : Category ℓo ℓt) (Vars : FinSet ℓ-zero)
      → (Vars .fst → Presheaf C ℓS) → Presheaf C ℓS
Πfinᴾ C Vars Ps .F-ob c = (∀ (x : Vars .fst) → (Ps x ⟅ c ⟆) .fst) , isSetΠ λ x → (Ps x ⟅ c ⟆) .snd
Πfinᴾ C Vars Ps .F-hom f ϕs x = C [ ϕs x ∘ᴾ⟨ Ps x ⟩ f ]
Πfinᴾ C Vars Ps .F-id = λ i ϕs x → ∘ᴾId C (Ps x) (ϕs x) i
Πfinᴾ C Vars Ps .F-seq = λ f g i ϕs x → ∘ᴾAssoc C (Ps x) (ϕs x) f g i

push-Πᴾ : {C : Category ℓc ℓc'} {D : Category ℓd ℓd'} (F : Functor C D)
        → (Vars : FinSet ℓ-zero) (obs : Vars .fst → C .ob)
        → PshHom F (Πfinᴾ C Vars λ x → C [-, obs x ] ) ((Πfinᴾ D Vars λ x → D [-, F ⟅ obs x ⟆ ] ))
push-Πᴾ F Vars obs .N-ob c fs = lift (λ x → F ⟪ fs .lower x ⟫)
push-Πᴾ F Vars obs .N-hom f = funExt (λ fs i → lift (λ x → F .F-seq f (fs .lower x) i))

Πᴾ : ∀ {ℓo ℓt ℓS} (C : Category ℓo ℓt)
              → (J : Type ℓp)
              → (J → Presheaf C ℓS)
              → Presheaf C (ℓ-max ℓS ℓp)
Πᴾ C J Ps .F-ob Γ = ((j : J) → fst (Ps j ⟅ Γ ⟆) ) , isSetΠ (λ j → snd (Ps j ⟅ Γ ⟆))
Πᴾ C J Ps .F-hom = λ γ ϕs j → C [ ϕs j ∘ᴾ⟨ Ps j ⟩ γ ]
Πᴾ C J Ps .F-id = funExt (λ ϕs i j → ∘ᴾId C (Ps j) (ϕs j) i)
Πᴾ C J Ps .F-seq δ γ = λ i ϕs j → ∘ᴾAssoc C (Ps j) (ϕs j) δ γ i

record CartesianCategory ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    cat : Category ℓ ℓ'
    finite-products : ∀ (J : FinSet ℓ-zero) → (obs : J .fst → cat .ob) → UnivElt cat (Πᴾ cat (J .fst) λ x → cat [-, obs x ])

  π : (J : FinSet ℓ-zero) → (obs : J .fst → cat .ob)
    → (j : J .fst) → cat [ finite-products J obs .vertex , obs j ]
  π J obs j = finite-products J obs .element j

open CartesianCategory

record CartesianFunctor (C : CartesianCategory ℓc ℓc') (D : CartesianCategory ℓd ℓd') : Type ((ℓ-max (ℓ-max (ℓ-max ℓc ℓc') ℓd) ℓd')) where
  field
    func : Functor (C .cat) (D .cat)
    preserves-terminal : preserves-⊤ func
    preserves-products : preserves-× func
