-- Free category over a directed graph/quiver
-- This time without any assumptions on the HLevels of the graph
{-# OPTIONS --safe #-}

module Cubical.Categories.Constructions.Free.General where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Data.Graph.Base

open import Cubical.Data.Graph.Properties

private
  variable
    ℓc ℓc' : Level

module _ {ℓv ℓe : Level} where
  module _ (G : Graph ℓv ℓe) where
    -- "Category expressions"
    data Exp : G .Node → G .Node → Type (ℓ-max ℓv ℓe) where
      ↑_   : ∀ {A B} → G .Edge A B → Exp A B
      idₑ  : ∀ {A} → Exp A A
      _⋆ₑ_ : ∀ {A B C} → Exp A B → Exp B C → Exp A C
      ⋆ₑIdL : ∀ {A B} (e : Exp A B) → idₑ ⋆ₑ e ≡ e
      ⋆ₑIdR : ∀ {A B} (e : Exp A B) → e ⋆ₑ idₑ ≡ e
      ⋆ₑAssoc : ∀ {A B C D} (e : Exp A B)(f : Exp B C)(g : Exp C D)
              → (e ⋆ₑ f) ⋆ₑ g ≡ e ⋆ₑ (f ⋆ₑ g)
      isSetExp : ∀ {A B} → isSet (Exp A B)

    open Category
    FreeCat : Category ℓv (ℓ-max ℓv ℓe)
    FreeCat .ob = G .Node
    FreeCat .Hom[_,_] = Exp
    FreeCat .id = idₑ
    FreeCat ._⋆_ = _⋆ₑ_
    FreeCat .⋆IdL = ⋆ₑIdL
    FreeCat .⋆IdR = ⋆ₑIdR
    FreeCat .⋆Assoc = ⋆ₑAssoc
    FreeCat .isSetHom = isSetExp

    -- Underlying graph of a category
    Ugr : ∀ {ℓc ℓc'} (𝓒 : Category ℓc ℓc') → Graph ℓc ℓc'
    Ugr 𝓒 .Node = 𝓒 .ob
    Ugr 𝓒 .Edge = 𝓒 .Hom[_,_]

    Uhom : ∀ {ℓc ℓc' ℓd ℓd'} {𝓒 : Category ℓc ℓc'} {𝓓 : Category ℓd ℓd'} (F : Functor 𝓒 𝓓)
         → GraphHom (Ugr 𝓒) (Ugr 𝓓)
    Uhom F ._$g_ = Functor.F-ob F
    Uhom F ._<$g>_ = Functor.F-hom F

    η : GraphHom G (Ugr FreeCat)
    η ._$g_ = λ z → z
    η ._<$g>_ = ↑_

    module Semantics {ℓc ℓc'} (𝓒 : Category ℓc ℓc') (ı : GraphHom G (Ugr 𝓒)) where
      -- Holy automatable argument batman
      ⟦_⟧ : ∀ {A B} → Exp A B → 𝓒 [ ı $g A , ı $g B ]
      ⟦ ↑ x ⟧ = ı <$g> x
      ⟦ idₑ ⟧ = 𝓒 .id
      ⟦ e ⋆ₑ e' ⟧ = ⟦ e ⟧ ⋆⟨ 𝓒 ⟩ ⟦ e' ⟧
      ⟦ ⋆ₑIdL e i ⟧ = 𝓒 .⋆IdL ⟦ e ⟧ i
      ⟦ ⋆ₑIdR e i ⟧ = 𝓒 .⋆IdR ⟦ e ⟧ i
      ⟦ ⋆ₑAssoc e e' e'' i ⟧ = 𝓒 .⋆Assoc ⟦ e ⟧ ⟦ e' ⟧ ⟦ e'' ⟧ i
      ⟦ isSetExp e e' p q i j ⟧ = 𝓒 .isSetHom ⟦ e ⟧ ⟦ e' ⟧ (cong ⟦_⟧ p) (cong ⟦_⟧ q) i j

      sem : Functor FreeCat 𝓒
      sem .Functor.F-ob v = ı $g v
      sem .Functor.F-hom e = ⟦ e ⟧
      sem .Functor.F-id = refl
      sem .Functor.F-seq e e' = refl

    module _ {𝓒 : Category ℓc ℓc'} (F : Functor FreeCat 𝓒) where
      open Semantics 𝓒 (η ⋆GrHom Uhom F)
      open Functor

      uniq-on-morphisms : ∀ {A B : G .Node} (e : FreeCat [ A , B ]) → F ⟪ e ⟫ ≡ ⟦ e ⟧
      uniq-on-morphisms (↑ x) = refl
      uniq-on-morphisms idₑ = F .F-id
      uniq-on-morphisms (e ⋆ₑ e') =
        F .F-seq e e'
        ∙ λ i → uniq-on-morphisms e i ⋆⟨ 𝓒 ⟩ uniq-on-morphisms e' i
      -- LMFAO
      -- This is thankfully completely mechanical from reading the
      -- goals, but not automatable for the time being
      uniq-on-morphisms (⋆ₑIdL f i) j =
        isSet→SquareP (λ _ _ → 𝓒 .isSetHom)
          (F .F-seq idₑ f ∙ (λ i₁ → seq' 𝓒 (F .F-id i₁) (uniq-on-morphisms f i₁)))
          (uniq-on-morphisms f)
          (λ i → F ⟪ ⋆ₑIdL f i ⟫)
          (λ i → ⟦ ⋆ₑIdL f i ⟧) i j
      uniq-on-morphisms (⋆ₑIdR f i) j =
        isSet→SquareP (λ _ _ → 𝓒 .isSetHom)
          (F .F-seq f idₑ ∙ (λ i₁ → seq' 𝓒 (uniq-on-morphisms f i₁) (F .F-id i₁)))
          (uniq-on-morphisms f)
          (λ i → F ⟪ ⋆ₑIdR f i ⟫)
          (λ i → ⟦ ⋆ₑIdR f i ⟧)
          i j
      uniq-on-morphisms (⋆ₑAssoc f f₁ f₂ i) =
        isSet→SquareP (λ _ _ → 𝓒 .isSetHom)
          ((F .F-seq (f ⋆ₑ f₁) f₂ ∙
          (λ i₁ →
             seq' 𝓒
             ((F .F-seq f f₁ ∙
               (λ i₂ → seq' 𝓒 (uniq-on-morphisms f i₂) (uniq-on-morphisms f₁ i₂)))
              i₁)
             (uniq-on-morphisms f₂ i₁))))
          ((F .F-seq f (f₁ ⋆ₑ f₂) ∙
          (λ i₁ →
             seq' 𝓒 (uniq-on-morphisms f i₁)
             ((F .F-seq f₁ f₂ ∙
               (λ i₂ →
                  seq' 𝓒 (uniq-on-morphisms f₁ i₂) (uniq-on-morphisms f₂ i₂)))
              i₁))))
          ((λ i → F ⟪ ⋆ₑAssoc f f₁ f₂ i ⟫))
          (λ i → ⟦ ⋆ₑAssoc f f₁ f₂ i ⟧)
          i
      uniq-on-morphisms (isSetExp e e' x y i j) =
        isSet→SquareP
          -- A very important trick
          (λ i j → isSet→isGroupoid (𝓒 .isSetHom) (F ⟪ isSetExp e e' x y i j ⟫) ⟦ isSetExp e e' x y i j ⟧)
          (λ j → uniq-on-morphisms (x j))
          (λ j → uniq-on-morphisms (y j))
          (λ i → uniq-on-morphisms e)
          (λ i → uniq-on-morphisms e')
          i j
