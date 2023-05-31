{-# OPTIONS --safe #-}
module Cubical.Categories.Comonad.Instances.Environment where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function renaming (_∘_ to _∘f_)
open import Cubical.Categories.Category hiding (isIso)
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Monad.Base
open import Cubical.Categories.Comonad.Base
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf.Representable

open import Cubical.Categories.DistributiveLaw.ComonadOverMonad.Base
open import Cubical.Tactics.FunctorSolver.Reflection
private
  variable
    ℓ ℓ' : Level

open IsComonad
open BinProduct
open NatTrans
open isUniversal
open UnivElt
open IsComonadHom

module _ {C : Category ℓ ℓ'} (Γ : Category.ob C) (Γ×- : ∀ c → BinProduct C Γ c) where
  open Category C
  open ProdsWithNotation C Γ×-
  Γ×-F : Functor C C
  Γ×-F = BinProductWithF C Γ×-

  Γ×-F-Como : IsComonad Γ×-F
  -- Naturality of ε, δ should follow from some more general fact about universal properties
  Γ×-F-Como .ε .N-ob x = π₂
  Γ×-F-Como .ε .N-hom {x}{y} f = ×β₂
  Γ×-F-Como .δ .N-ob x = π₁ ,p id
  Γ×-F-Como .δ .N-hom {x}{y} f =
    ,p-natural
    ∙ cong₂ _,p_
       (×β₁ ∙ refl ∙ sym ×β₁)
       (⋆IdR _
       ∙ (cong₂ _,p_ (sym (⋆IdL _) ∙ cong₂ _∘_ refl (sym ×β₂) ∙ ⋆Assoc _ _ _)
                     (sym (⋆IdL _) ∙ cong₂ _∘_ refl (sym ×β₂) ∙ ⋆Assoc _ _ _)
       ∙ sym ,p-natural)
       ∙ cong₂ _⋆_ refl (sym ,p-natural))
    ∙ sym ,p-natural
  Γ×-F-Como .idl-δ = makeNatTransPathP refl (F-rUnit {F = Γ×-F})
    (funExt λ x → ×β₂)
  Γ×-F-Como .idr-δ = makeNatTransPathP refl (F-lUnit {F = Γ×-F})
    (funExt λ x → ,p-natural ∙ cong₂ _,p_ ×β₁ (sym (⋆Assoc _ _ _) ∙ cong₂ _∘_ refl ×β₂ ∙ ⋆IdL _)
      ∙ sym ×η')
  Γ×-F-Como .assoc-δ =
    ,p-natural
    ∙ cong₂ _,p_ refl
      ((sym (⋆Assoc _ _ _) ∙ cong₂ _⋆_ ×β₂ refl ∙ ⋆IdL _) ∙ sym (⋆IdR _))
    ∙ sym ,p-natural

  Env : Comonad C
  Env = Γ×-F , Γ×-F-Como

module _ {C : Category ℓ ℓ'} (bp : BinProducts C) where
  open Category C
  open Notation C bp
  open Functor
  Env' : ob → Comonad C
  Env' Γ = Env Γ (bp Γ)

  push : {Δ Γ : ob} (γ : Hom[ Δ , Γ ]) → ComonadHom (Env Δ (bp Δ)) (Env Γ (bp Γ))
  push γ .fst .N-ob x = γ ×p id
  push γ .fst .N-hom f =
    ,p-natural
    ∙ cong₂ _,p_
            (sym (⋆Assoc _ _ _) ∙ cong₂ _∘_ refl ×β₁ ∙ sym ×β₁)
            (cong₂ _⋆_ refl (⋆IdR _)  ∙ ×β₂ ∙ cong₂ _∘_ refl (sym (⋆IdR _) ∙ sym ×β₂) ∙ ⋆Assoc _ _ _)
    ∙ sym ,p-natural
  push γ .snd .V-ε = makeNatTransPath (funExt λ x → ×β₂ ∙ ⋆IdR _)
  push γ .snd .V-δ = makeNatTransPath (funExt λ x →
  -- my kingdom for a product solver
    ,p-natural
    ∙ cong₂ _,p_
      (×β₁
      ∙ (cong₂ _∘_ refl (sym ×β₁) ∙ ⋆Assoc _ _ _)
      ∙ cong₂ _⋆_ refl (cong₂ _∘_ refl (sym ×β₁) ∙ ⋆Assoc _ _ _))
      (⋆IdR _
      ∙ (×-extensionality (×β₁ ∙ (sym (⋆IdL _) ∙ cong₂ _⋆_ (sym ×β₂) refl ∙ ⋆Assoc _ _ _) ∙ cong₂ _⋆_ refl (cong₂ _⋆_ refl (sym ×β₁) ∙ sym (⋆Assoc _ _ _)) ∙ sym (⋆Assoc _ _ _))
                          (×β₂ ∙ ⋆IdR _ ∙ (((sym (⋆IdL _) ∙ cong₂ _∘_ refl (sym ×β₂)) ∙ ⋆Assoc _ _ _) ∙ cong₂ _⋆_ refl (sym ×β₂) ∙ sym (⋆Assoc _ _ _)) ∙ cong₂ _⋆_ (cong₂ _⋆_ refl (cong₂ _,p_ refl (cong₂ _⋆_ refl (sym (⋆IdR _))) ∙ sym ,p-natural)) refl)
        ∙ cong₂ _⋆_ refl (sym ×β₂))
      ∙ cong₂ _⋆_ refl (cong₂ _⋆_ refl (sym (⋆IdR _))))
    ∙ sym ,p-natural ∙ cong₂ _⋆_ refl (sym ,p-natural))

  push-id : ∀ {Γ} → push (id {Γ}) .fst ≡ idTrans (Env' Γ .fst)
  push-id = makeNatTransPath (funExt λ x → ×pF .F-id)

  push-comp : ∀ {Θ Δ Γ} (γ : Hom[ Δ , Γ ])(δ : Hom[ Θ , Δ ])
          → push (γ ∘ δ) .fst ≡ push γ .fst ∘ᵛ push δ .fst
  push-comp γ δ = makeNatTransPath (funExt λ x →
    cong₂ _,p_ (sym (⋆Assoc _ _ _) ∙ cong₂ _∘_ refl (sym ×β₁) ∙ ⋆Assoc _ _ _)
               (⋆IdR _ ∙ (sym (⋆IdR _) ∙ sym ×β₂) ∙ cong₂ _⋆_ refl (sym (⋆IdR _) ))
    ∙ sym ,p-natural)
