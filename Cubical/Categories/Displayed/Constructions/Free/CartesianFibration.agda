{-
  The free cartesian fibration generated by ...
-}

{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Constructions.Free.CartesianFibration where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Displayed.Limits.BinProduct.Concrete
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Displayed.Limits.Terminal.Concrete
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Terminal.More
open import Agda.Builtin.Cubical.Equiv
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Foundations.Univalence

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓCᴰᴰ ℓCᴰᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category
module FreeCartesianFibration
  (C : Category ℓC ℓC')
  (GOb : C .ob → Type ℓCᴰ)
  where
  
  data Ob (x : C .ob) : Type (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) where
    iOb : GOb x → Ob x
    ⊤ₑ : Ob x
    _∧ₑ_ : Ob x → Ob x → Ob x
    pullbackₑ : ∀ {y} (f : C [ x , y ]) → Ob y → Ob x

  module _ (GHom : ∀ {x}{y} (f : C [ x , y ]) → Type ℓCᴰ')
    (GHomDom : ∀ {x}{y} {f : C [ x , y ]} → GHom f → Ob x)
    (GHomCod : ∀ {x}{y} {f : C [ x , y ]} → GHom f → Ob y)
    where
    data Homₑ : ∀ {x y} (f : C [ x , y ]) → Ob x → Ob y → Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓCᴰ ℓCᴰ'))
    -- if we added a vertical hom we can avoid some PathPs, not sure if we care tho
    _≡[_]ₑ_ : ∀ {x y} {xᴰ yᴰ} {f f' : C [ x , y ]}
      → Homₑ f xᴰ yᴰ
      → f ≡ f'
      → Homₑ f' xᴰ yᴰ
      → Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) ℓCᴰ')
    _≡[_]ₑ_ {xᴰ = xᴰ}{yᴰ} fᴰ p fᴰ' = PathP (λ i → Homₑ (p i) xᴰ yᴰ) fᴰ fᴰ'
    data Homₑ where
      iHom : ∀ {x y} {f : C [ x , y ]} → (fᴰ : GHom f)
        → Homₑ f (GHomDom fᴰ) (GHomCod fᴰ)
      idᴰₑ : ∀ {x} {xᴰ} → Homₑ (C .id {x}) xᴰ xᴰ
      _⋆ᴰₑ_ : ∀ {x y z} {xᴰ yᴰ zᴰ} {f : C [ x , y ]}{g : C [ y , z ]}
        → Homₑ f xᴰ yᴰ
        → Homₑ g yᴰ zᴰ
        → Homₑ (f ⋆⟨ C ⟩ g) xᴰ zᴰ
      ⋆IdLᴰₑ : ∀ {x y} {xᴰ yᴰ} {f : C [ x , y ]}
        → (fᴰ : Homₑ f xᴰ yᴰ)
        → (idᴰₑ ⋆ᴰₑ fᴰ) ≡[ C .⋆IdL f ]ₑ fᴰ
      ⋆IdRᴰₑ : ∀ {x y} {xᴰ yᴰ} {f : C [ x , y ]}
        → (fᴰ : Homₑ f xᴰ yᴰ)
        → (fᴰ ⋆ᴰₑ idᴰₑ) ≡[ C .⋆IdR f ]ₑ fᴰ
      ⋆Assocᴰₑ : ∀ {w x y z} {wᴰ xᴰ yᴰ zᴰ}
        {f : C [ w , x ]}{g : C [ x , y ]}{h : C [ y , z ]}
        (fᴰ : Homₑ f wᴰ xᴰ)
        (gᴰ : Homₑ g xᴰ yᴰ)
        (hᴰ : Homₑ h yᴰ zᴰ)
        → ((fᴰ ⋆ᴰₑ gᴰ) ⋆ᴰₑ hᴰ) ≡[ C .⋆Assoc f g h ]ₑ (fᴰ ⋆ᴰₑ (gᴰ ⋆ᴰₑ hᴰ))
      !ᴰₑ : ∀ {x y}{xᴰ} (f : C [ x , y ]) → Homₑ f xᴰ ⊤ₑ
      ⊤η :  ∀ {x y}{xᴰ} {f : C [ x , y ]} (fᴰ : Homₑ f xᴰ ⊤ₑ) → fᴰ ≡ !ᴰₑ f
      π₁ᴰₑ : ∀ {x}{xᴰ₁ xᴰ₂} → Homₑ (C .id {x}) (xᴰ₁ ∧ₑ xᴰ₂) xᴰ₁
      π₂ᴰₑ : ∀ {x}{xᴰ₁ xᴰ₂} → Homₑ (C .id {x}) (xᴰ₁ ∧ₑ xᴰ₂) xᴰ₂
      _,pₑ_ : ∀ {x y} {xᴰ₁ xᴰ₂ yᴰ} {f : C [ y , x ]}
        → Homₑ f yᴰ xᴰ₁
        → Homₑ f yᴰ xᴰ₂
        → Homₑ f yᴰ (xᴰ₁ ∧ₑ xᴰ₂)
      ∧β₁ₑ :  ∀ {x y} {xᴰ₁ xᴰ₂ yᴰ} {f : C [ y , x ]}
        → (fᴰ₁ : Homₑ f yᴰ xᴰ₁)
        → (fᴰ₂ : Homₑ f yᴰ xᴰ₂)
        → ((fᴰ₁ ,pₑ fᴰ₂) ⋆ᴰₑ π₁ᴰₑ) ≡[ C .⋆IdR f ]ₑ fᴰ₁
      ∧β₂ₑ :  ∀ {x y} {xᴰ₁ xᴰ₂ yᴰ} {f : C [ y , x ]}
        → (fᴰ₁ : Homₑ f yᴰ xᴰ₁)
        → (fᴰ₂ : Homₑ f yᴰ xᴰ₂)
        → ((fᴰ₁ ,pₑ fᴰ₂) ⋆ᴰₑ π₂ᴰₑ) ≡[ C .⋆IdR f ]ₑ fᴰ₂
      ∧ηₑ : ∀ {x y} {xᴰ₁ xᴰ₂ yᴰ} {f : C [ y , x ]}
        → (fᴰ : Homₑ f yᴰ (xᴰ₁ ∧ₑ xᴰ₂))
        → fᴰ ≡[ sym (C .⋆IdR f) ]ₑ ((fᴰ ⋆ᴰₑ π₁ᴰₑ) ,pₑ (fᴰ ⋆ᴰₑ π₂ᴰₑ))

      pb-πₑ : ∀ {x y}{yᴰ}{g : C [ x , y ]} → Homₑ g (pullbackₑ g yᴰ) yᴰ
      pb-introₑ :
        ∀ {x y z}{zᴰ yᴰ}{f : C [ z , x ]}{g : C [ x , y ]}
        → Homₑ (f ⋆⟨ C ⟩ g) zᴰ yᴰ
        → Homₑ f zᴰ (pullbackₑ g yᴰ)
      pb-βₑ :
        ∀ {x y z}{zᴰ yᴰ}{f : C [ z , x ]}{g : C [ x , y ]}
        → (fgᴰ : Homₑ (f ⋆⟨ C ⟩ g) zᴰ yᴰ)
        → (pb-introₑ fgᴰ ⋆ᴰₑ pb-πₑ) ≡ fgᴰ
      pb-ηₑ :
        ∀ {x y z}{zᴰ yᴰ}{f : C [ z , x ]}{g : C [ x , y ]}
        → (fᴰ : Homₑ f zᴰ (pullbackₑ g yᴰ))
        → fᴰ ≡ pb-introₑ (fᴰ ⋆ᴰₑ pb-πₑ)
      isSetHomᴰₑ : ∀ {x y}{xᴰ yᴰ}{f : C [ x , y ]} → isSet (Homₑ f xᴰ yᴰ)

    open Categoryᴰ
    FreeCartFib : Categoryᴰ C (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) ℓCᴰ')
    FreeCartFib .ob[_] = Ob
    FreeCartFib .Hom[_][_,_] = Homₑ
    FreeCartFib .idᴰ = idᴰₑ
    FreeCartFib ._⋆ᴰ_ = _⋆ᴰₑ_
    FreeCartFib .⋆IdLᴰ = ⋆IdLᴰₑ
    FreeCartFib .⋆IdRᴰ = ⋆IdRᴰₑ
    FreeCartFib .⋆Assocᴰ = ⋆Assocᴰₑ
    FreeCartFib .isSetHomᴰ = isSetHomᴰₑ

    -- elimination principle:
    module _ (Cᴰ : Categoryᴰ C ℓCᴰᴰ ℓCᴰᴰ')
      (isFibCᴰ : AllCartesianOvers Cᴰ)
      (verticalTerminalsCᴰ : VerticalTerminals Cᴰ)
      (verticalBinProductsCᴰ : VerticalBinProducts Cᴰ)
      where
      private
        module Cᴰ = Categoryᴰ Cᴰ
        module R = HomᴰReasoning Cᴰ
        open UniversalElementᴰ
        open VerticalTerminal
        open VerticalBinProduct
        open CartesianOver
        open Section
      module _ (iObᴰ : ∀ {x} → GOb x → Cᴰ.ob[ x ]) where
        rec-F-obᴰ : ∀ {x} → Ob x → Cᴰ.ob[ x ]
        rec-F-obᴰ (iOb xᴰ) = iObᴰ xᴰ
        rec-F-obᴰ ⊤ₑ = verticalTerminalsCᴰ _ .⊤ᴰ
        rec-F-obᴰ (xᴰ₁ ∧ₑ xᴰ₂) =
          verticalBinProductsCᴰ _ (rec-F-obᴰ xᴰ₁) (rec-F-obᴰ xᴰ₂) .prodᴰ
        rec-F-obᴰ (pullbackₑ f xᴰ) = isFibCᴰ (rec-F-obᴰ xᴰ) f .f*cᴰ'

        module _ (iHomᴰ : ∀ {x y} {f : C [ x , y ]} → (g : GHom f)
                 → Cᴰ.Hom[ f ][ rec-F-obᴰ (GHomDom g) , rec-F-obᴰ (GHomCod g) ])
               where
          rec-F-homᴰ : ∀ {x y}{f : C [ x , y ]}{xᴰ yᴰ} → Homₑ f xᴰ yᴰ
            → Cᴰ.Hom[ f ][ rec-F-obᴰ xᴰ , rec-F-obᴰ yᴰ ]
          rec-F-homᴰ (iHom fᴰ) = iHomᴰ fᴰ
          rec-F-homᴰ idᴰₑ = Cᴰ.idᴰ
          rec-F-homᴰ (fᴰ ⋆ᴰₑ gᴰ) = rec-F-homᴰ fᴰ Cᴰ.⋆ᴰ rec-F-homᴰ gᴰ
          rec-F-homᴰ (⋆IdLᴰₑ fᴰ i) = Cᴰ.⋆IdLᴰ (rec-F-homᴰ fᴰ) i
          rec-F-homᴰ (⋆IdRᴰₑ fᴰ i) = Cᴰ.⋆IdRᴰ (rec-F-homᴰ fᴰ) i
          rec-F-homᴰ (⋆Assocᴰₑ fᴰ gᴰ hᴰ i) =
            Cᴰ.⋆Assocᴰ (rec-F-homᴰ fᴰ) (rec-F-homᴰ gᴰ) (rec-F-homᴰ hᴰ) i
          rec-F-homᴰ (!ᴰₑ _) = verticalTerminalsCᴰ _ .corecᴰ
          rec-F-homᴰ (⊤η fᴰ i) = verticalTerminalsCᴰ _ .ηᴰ (rec-F-homᴰ fᴰ) i
          rec-F-homᴰ π₁ᴰₑ = verticalBinProductsCᴰ _ _ _ .π₁ᴰ
          rec-F-homᴰ π₂ᴰₑ = verticalBinProductsCᴰ _ _ _ .π₂ᴰ
          rec-F-homᴰ (fᴰ₁ ,pₑ fᴰ₂) =
            verticalBinProductsCᴰ _ _ _ ._,pᴰ_ (rec-F-homᴰ fᴰ₁) (rec-F-homᴰ fᴰ₂)
          rec-F-homᴰ (∧β₁ₑ fᴰ₁ fᴰ₂ i) =
            verticalBinProductsCᴰ _ _ _ .β₁ᴰ (rec-F-homᴰ fᴰ₁) (rec-F-homᴰ fᴰ₂) i
          rec-F-homᴰ (∧β₂ₑ fᴰ₁ fᴰ₂ i) =
            verticalBinProductsCᴰ _ _ _ .β₂ᴰ (rec-F-homᴰ fᴰ₁) (rec-F-homᴰ fᴰ₂) i
          rec-F-homᴰ (∧ηₑ fᴰ i) =
            verticalBinProductsCᴰ _ _ _ .ηᴰ (rec-F-homᴰ fᴰ) i
          rec-F-homᴰ pb-πₑ = isFibCᴰ _ _ .π
          rec-F-homᴰ (pb-introₑ fᴰ) = corec (isFibCᴰ _ _) _ _ (rec-F-homᴰ fᴰ) 
          rec-F-homᴰ (pb-βₑ fᴰ i) = corec-β (isFibCᴰ _ _) _ _ (rec-F-homᴰ fᴰ) i
          rec-F-homᴰ (pb-ηₑ fᴰ i) = corec-η (isFibCᴰ _ _) _ _ (rec-F-homᴰ fᴰ) i
          rec-F-homᴰ (isSetHomᴰₑ fᴰ gᴰ p q i j) =
            Cᴰ.isSetHomᴰ (rec-F-homᴰ fᴰ) (rec-F-homᴰ gᴰ)
                         (cong rec-F-homᴰ p) (cong rec-F-homᴰ q)
                         i j
    module _ (Cᴰ : Categoryᴰ (∫C FreeCartFib) ℓCᴰᴰ ℓCᴰᴰ')
      (isFibCᴰ : AllCartesianOvers Cᴰ)
      (verticalTerminalsCᴰ : VerticalTerminals Cᴰ)
      (verticalBinProductsCᴰ : VerticalBinProducts Cᴰ)
      where
      private
        module Cᴰ = Categoryᴰ Cᴰ
        module R = HomᴰReasoning Cᴰ
        open UniversalElementᴰ
        open CartesianOver
        open VerticalBinProduct
        open Section

      module _ (iObᴰ : ∀ x → (xᴰ : GOb x) → Cᴰ.ob[ x , iOb xᴰ ]) where
    --     elim-F-obᴰ : ∀ x xᴰ → Cᴰ.ob[ x , xᴰ ]
    --     elim-F-obᴰ x (iOb xᴰ) = iObᴰ x xᴰ
    --     elim-F-obᴰ x ⊤ₑ = verticalTerminalsCᴰ (x , ⊤ₑ) .vertexᴰ
    --     elim-F-obᴰ x (xᴰ₁ ∧ₑ xᴰ₂) =
    --       verticalBinProductsCᴰ _
    --         (isFibCᴰ (elim-F-obᴰ x xᴰ₁) ((C .id) , π₁ᴰₑ) .f*cᴰ' )
    --         (isFibCᴰ (elim-F-obᴰ x xᴰ₂) ((C .id) , π₂ᴰₑ) .f*cᴰ')
    --         .prodᴰ
    --     elim-F-obᴰ x (pullbackₑ {y = y} f yᴰ) =
    --       isFibCᴰ (elim-F-obᴰ y yᴰ) (f , pb-πₑ) .f*cᴰ'
    --     module _ (iHomᴰ : ∀ {x y}(f : C [ x , y ])(fᴰ : GHom f)
    --              → Cᴰ.Hom[ f , iHom fᴰ ][ elim-F-obᴰ x (GHomDom fᴰ)
    --                                    , elim-F-obᴰ y (GHomCod fᴰ) ])
    --            where

    --       elim : GlobalSection Cᴰ
    --       elim .F-obᴰ (x , xᴰ) = elim-F-obᴰ x xᴰ
    --       elim .F-homᴰ (f , fᴰ) = elim-F-homᴰ fᴰ
    --       elim .F-idᴰ = refl
    --       elim .F-seqᴰ = λ f g → refl
