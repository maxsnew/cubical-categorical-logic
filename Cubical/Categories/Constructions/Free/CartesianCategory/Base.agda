{-# OPTIONS --safe #-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Constructions.Free.CartesianCategory.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma hiding (_×_)

open import
  Cubical.Categories.Constructions.Free.CartesianCategory.ProductQuiver
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinProduct.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.More
open import Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Displayed.Limits.Cartesian
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Constructions.Reindex.Base
open import Cubical.Categories.Displayed.Constructions.Reindex.Properties
open import Cubical.Categories.Displayed.Constructions.Reindex.Limits
  as CartReindex
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Constructions.Weaken as Wk

private
  variable
    ℓQ ℓQ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

module _ (Q : ×Quiver ℓQ ℓQ') where
  open ProductQuiver
  private module Q = ×QuiverNotation Q
  data Exp : Q.Ob → Q.Ob → Type (ℓ-max ℓQ ℓQ') where
    ↑ₑ_ : ∀ t → Exp (Q.Dom t) (Q.Cod t)
    idₑ : ∀{Γ} → Exp Γ Γ
    _⋆ₑ_ : ∀{Γ Γ' Γ''}(δ : Exp Γ Γ') → (δ' : Exp Γ' Γ'') →  Exp Γ Γ''
    ⋆ₑIdL : ∀{Γ Δ}(δ : Exp Γ Δ) → idₑ ⋆ₑ δ ≡ δ
    ⋆ₑIdR : ∀{Γ Δ}(δ : Exp Γ Δ) → δ ⋆ₑ idₑ ≡ δ
    ⋆ₑAssoc : ∀{Γ Γ' Γ'' Γ'''}
      (δ : Exp Γ Γ')(δ' : Exp Γ' Γ'')(δ'' : Exp Γ'' Γ''')
      → (δ ⋆ₑ δ') ⋆ₑ δ'' ≡ δ ⋆ₑ (δ' ⋆ₑ δ'')
    isSetExp : ∀{Γ Γ'} → isSet (Exp Γ Γ')
    !ₑ : ∀{Γ} → Exp Γ ⊤
    ⊤η : ∀{Γ}(t : Exp Γ ⊤) → t ≡ !ₑ
    π₁ : ∀{Γ Δ} → Exp (Γ × Δ) Γ
    π₂ : ∀{Γ Δ} → Exp (Γ × Δ) Δ
    ⟨_,_⟩ : ∀{Γ Δ Δ'} → Exp Γ Δ → Exp Γ Δ' → Exp Γ (Δ × Δ')
    ×β₁ : ∀{Γ Δ Δ'}{t : Exp Γ Δ}{t' : Exp Γ Δ'} → ⟨ t , t' ⟩ ⋆ₑ π₁ ≡ t
    ×β₂ : ∀{Γ Δ Δ'}{t : Exp Γ Δ}{t' : Exp Γ Δ'} → ⟨ t , t' ⟩ ⋆ₑ π₂ ≡ t'
    ×η : ∀{Γ Δ Δ'}{t : Exp Γ (Δ × Δ')} → t ≡ ⟨ t ⋆ₑ π₁ , t ⋆ₑ π₂ ⟩

  open Category
  |FreeCartesianCategory| : Category _ _
  |FreeCartesianCategory| .ob = Q.Ob
  |FreeCartesianCategory| .Hom[_,_] = Exp
  |FreeCartesianCategory| .id = idₑ
  |FreeCartesianCategory| ._⋆_ = _⋆ₑ_
  |FreeCartesianCategory| .⋆IdL = ⋆ₑIdL
  |FreeCartesianCategory| .⋆IdR = ⋆ₑIdR
  |FreeCartesianCategory| .⋆Assoc = ⋆ₑAssoc
  |FreeCartesianCategory| .isSetHom = isSetExp

  FreeCartesianCategory : CartesianCategory _ _
  FreeCartesianCategory .fst = |FreeCartesianCategory|
  FreeCartesianCategory .snd .fst = ⊤ , λ Γ → !ₑ , λ t → sym (⊤η t)
  FreeCartesianCategory .snd .snd Γ Δ .BinProduct.binProdOb = Γ × Δ
  FreeCartesianCategory .snd .snd Γ Δ .BinProduct.binProdPr₁ = π₁
  FreeCartesianCategory .snd .snd Γ Δ .BinProduct.binProdPr₂ = π₂
  FreeCartesianCategory .snd .snd Γ Δ .BinProduct.univProp f g = uniqueExists
    ⟨ f , g ⟩
    (×β₁ , ×β₂)
    (λ _ → isProp× (isSetExp _ _) (isSetExp _ _))
    λ ⟨f,g⟩' (comm₁ , comm₂) → cong₂ ⟨_,_⟩ (sym comm₁) (sym comm₂) ∙ sym ×η

  module _
    (CCᴰ : CartesianCategoryᴰ FreeCartesianCategory ℓCᴰ ℓCᴰ')
    where
    private
      Cᴰ = CCᴰ .fst
      module Cᴰ = Categoryᴰ Cᴰ
      termᴰ = CCᴰ .snd .fst
      bpᴰ = CCᴰ .snd .snd
      open TerminalᴰNotation _ termᴰ
      open hasAllBinProductᴰNotation bpᴰ
    open UniversalElementᴰ
    module _ (ı-ob : ∀ o → Cᴰ.ob[ ↑ o ]) where
      elim-F-ob : ∀ c → Cᴰ.ob[ c ]
      elim-F-ob (↑ o)     = ı-ob o
      elim-F-ob ⊤         = 𝟙ᴰ
      elim-F-ob (c₁ × c₂) = elim-F-ob c₁ ×ᴰ elim-F-ob c₂


    record Interpᴰ : Type (ℓ-max (ℓ-max ℓQ ℓQ') (ℓ-max ℓCᴰ ℓCᴰ')) where
      constructor mkInterpᴰ
      field
        ı-ob : ∀ o → Cᴰ.ob[ ↑ o ]
        ı-hom : ∀ e
          → Cᴰ.Hom[ ↑ₑ e ][ elim-F-ob ı-ob (Q.Dom e)
                         , elim-F-ob ı-ob (Q.Cod e) ]
    module _ (ı : Interpᴰ)
        where
        open Section
        open Interpᴰ ı
        private
          module R = HomᴰReasoning Cᴰ

        elim-F-hom : ∀ {c c'} (f : |FreeCartesianCategory| [ c , c' ]) →
          Cᴰ [ f ][ elim-F-ob ı-ob c , elim-F-ob ı-ob c' ]
        elim-F-hom (↑ₑ t) = ı-hom t
        elim-F-hom idₑ = Cᴰ.idᴰ
        elim-F-hom (f ⋆ₑ g) = elim-F-hom f Cᴰ.⋆ᴰ elim-F-hom g
        elim-F-hom (⋆ₑIdL f i) = Cᴰ.⋆IdLᴰ (elim-F-hom f) i
        elim-F-hom (⋆ₑIdR f i) = Cᴰ.⋆IdRᴰ (elim-F-hom f) i
        elim-F-hom (⋆ₑAssoc f g h i) =
          Cᴰ.⋆Assocᴰ (elim-F-hom f) (elim-F-hom g) (elim-F-hom h) i
        elim-F-hom (isSetExp f g p q i j) =
          isSetHomᴰ' Cᴰ
          (elim-F-hom f) (elim-F-hom g)
          (cong elim-F-hom p) (cong elim-F-hom q)
          i j
        elim-F-hom !ₑ = !tᴰ _
        elim-F-hom (⊤η f i) =
          R.rectify {p' = ⊤η f} (𝟙ηᴰ (elim-F-hom f)) i
        elim-F-hom π₁ = π₁ᴰ
        elim-F-hom π₂ = π₂ᴰ
        elim-F-hom ⟨ f₁ , f₂ ⟩ = elim-F-hom f₁ ,pᴰ elim-F-hom f₂
        elim-F-hom (×β₁ {t = f₁}{t' = f₂} i) =
          R.rectify {p' = ×β₁}
            ((×β₁ᴰ {f₁ᴰ = elim-F-hom f₁} {f₂ᴰ = elim-F-hom f₂})) i
        elim-F-hom (×β₂ {t = f₁}{t' = f₂} i) =
          R.rectify {p' = ×β₂}
            (×β₂ᴰ {f₁ᴰ = elim-F-hom f₁} {f₂ᴰ = elim-F-hom f₂}) i
        elim-F-hom (×η {t = f} i) =
          R.rectify {p' = ×η {t = f}} (×ηᴰ {fᴰ = elim-F-hom f}) i

        elim : GlobalSection Cᴰ
        elim .F-obᴰ = elim-F-ob ı-ob
        elim .F-homᴰ = elim-F-hom
        elim .F-idᴰ = refl
        elim .F-seqᴰ _ _ = refl

  module _
    {D : Category ℓD ℓD'}
    {F : Functor |FreeCartesianCategory| D}
    (Dᴰ : CartesianCategoryⱽ D ℓDᴰ ℓDᴰ') where
    private
      module Dᴰ = Categoryᴰ (Dᴰ .fst)
      F*Dᴰ-cartⱽ = CartReindex.reindex F Dᴰ
      F*Dᴰ-cartᴰ =
        CartesianCategoryⱽ→CartesianCategoryᴰ FreeCartesianCategory F*Dᴰ-cartⱽ

    elimLocal : ∀ (ı : Interpᴰ F*Dᴰ-cartᴰ) → Section F (Dᴰ .fst)
    elimLocal ı = GlobalSectionReindex→Section (Dᴰ .fst) F
        (elim F*Dᴰ-cartᴰ ı)

  module _ (C : CartesianCategory ℓC ℓC') where
    private
      wkC = weakenCartesianCategory FreeCartesianCategory C
    -- TODO: rec preserves finite products, should follow from
    -- properties of weaken/elim preserved displayed fin products
    rec : (ı : Interpᴰ wkC) → Functor |FreeCartesianCategory| (C .fst)
    rec ı = introS⁻ (elim wkC ı)
