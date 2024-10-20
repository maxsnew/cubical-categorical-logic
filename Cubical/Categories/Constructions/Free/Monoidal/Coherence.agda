{- Coherence theorem for free monoidal categories on a set -}
{- Free monoidal category generated by a type of objects -}
{-# OPTIONS --safe #-}
module Cubical.Categories.Constructions.Free.Monoidal.Coherence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.List as List hiding ([_]; rec)

open import Cubical.Categories.Category.Base
open import Cubical.Categories.HLevels
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Instances.Discrete
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Functor
open import Cubical.Categories.Monoidal.Properties
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Constructions.Free.Category hiding (ε)

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.More
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.NaturalIsomorphism
open import Cubical.Categories.Displayed.Section
open import Cubical.Categories.Displayed.Monoidal.Base
open import Cubical.Categories.Displayed.Constructions.Reindex.Base
open import Cubical.Categories.Displayed.Constructions.Weaken.Monoidal
import Cubical.Categories.Displayed.Constructions.Weaken as Wk
open import Cubical.Categories.Displayed.Instances.Arrow.Base
open import Cubical.Categories.Displayed.Instances.Arrow.Monoidal

open import Cubical.Categories.Constructions.Free.Monoidal.Base as FreeMonoidal
  hiding (rec)

private
  variable
    ℓ ℓQ ℓQ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category
open Functor
open NatTrans
open NatIso
open isIso
module _ (X : hSet ℓ) where
  private
    |L| = DiscreteCategory
      ((List ⟨ X ⟩) , (isSet→isGroupoid (isOfHLevelList 0 (X .snd))))

    isThinL : hasPropHoms |L|
    isThinL = isOfHLevelList 0 (X .snd) _ _

    -- todo: generalize, discreteCat of any monoid is monoidal
    L : MonoidalCategory ℓ ℓ
    L = MonoidalPreorder→MonoidalCategory (record
      { C = |L|
      ; isPropHom = isThinL
      ; unit = []
      ; ─⊗─ = mkFunctor |L| isThinL
        (λ x → x .fst ++ x .snd)
        λ x → cong₂ _++_ (x .fst) (x .snd)
      ; α⟨_,_,_⟩ = λ x y z → sym (++-assoc x y z)
      ; α⁻¹⟨_,_,_⟩ = ++-assoc
      ; η⟨_⟩ = λ _ → refl
      ; η⁻¹⟨_⟩ = λ _ → refl
      ; ρ⟨_⟩ = λ x → ++-unit-r x
      ; ρ⁻¹⟨_⟩ = λ x → sym (++-unit-r x)
      })
    module L = MonoidalCategory L

  module _ (M : MonoidalCategory ℓC ℓC') where
    private
      module M = MonoidalCategory M

    module _ (ı : ⟨ X ⟩ → M.ob) where
      rec-ob : List ⟨ X ⟩ → M.ob
      rec-ob [] = M.unit
      rec-ob (x ∷ xs) = ı x M.⊗ rec-ob xs

      |rec| : Functor L.C M.C
      |rec| = DiscFunc rec-ob

      open StrongMonoidalFunctor
      open StrongMonoidalStr
      open LaxMonoidalStr

      |μ| : ∀ xs ys
        → CatIso M.C
            ((|rec| ⟅ xs ⟆) M.⊗ (|rec| ⟅ ys ⟆))
            (|rec| ⟅ xs ++ ys ⟆)
      |μ| [] ys = NatIsoAt M.η (|rec| ⟅ ys ⟆)
      |μ| (x ∷ xs) ys =
        ⋆Iso
          (invIso (NatIsoAt M.α _))
          (F-Iso {F = M.─⊗─} (CatIso× M.C M.C idCatIso (|μ| xs ys)))

      μ-nat :
        ∀ {xs xs'}
        → (p : xs ≡ xs')
        → ∀ {ys ys'}
        → (q : ys ≡ ys')
        → ((|rec| ⟪ p ⟫) M.⊗ₕ (|rec| ⟪ q ⟫)) M.⋆ |μ| xs' ys' .fst
          ≡ |μ| xs ys .fst M.⋆ (|rec| ⟪ cong₂ _++_ p q ⟫)
      μ-nat {xs} = J (λ xs' (p : xs ≡ xs') →
                       ∀ {ys} {ys'} →
                       (q : ys ≡ ys') →
                       (((|rec| ⟪ p ⟫) M.⊗ₕ (|rec| ⟪ q ⟫)) M.⋆ |μ| xs' ys' .fst) ≡
                       (|μ| xs ys .fst M.⋆ (|rec| ⟪ cong₂ _++_ p q ⟫)))
        λ {ys} → J
                  (λ ys' (q : ys ≡ ys') →
                     (((|rec| ⟪ refl {x = xs} ⟫) M.⊗ₕ (|rec| ⟪ q ⟫)) M.⋆ |μ| xs ys' .fst) ≡
                     (|μ| xs ys .fst M.⋆ (|rec| ⟪ cong₂ _++_ (refl {x = xs}) q ⟫)))

        (cong₂ M._⋆_ ((M.─⊗─ ∘F (|rec| ×F |rec|)) .F-id {x = (xs , ys)}) refl
        ∙ M.⋆IdL _
        ∙ sym (M.⋆IdR _)
        ∙ cong₂ M._⋆_ refl (sym (|rec| .F-id {x = xs ++ ys})))

      ρ∷ : ∀ x xs → L.ρ⟨ x ∷ xs ⟩ ≡ (refl {x = (x ∷ [])} L.⊗ₕ L.ρ⟨ xs ⟩)
      ρ∷ x xs = refl

      rec∷ : ∀ {x}{xs ys} (ps : xs ≡ ys)
        → |rec| ⟪ cong (x ∷_) ps ⟫
          ≡ M.id M.⊗ₕ |rec| ⟪ ps ⟫
      rec∷ {x}{xs}{ys} =
        J (λ ys ps → |rec| ⟪ cong (x ∷_) ps ⟫ ≡ M.id M.⊗ₕ |rec| ⟪ ps ⟫ )
          (|rec| .F-id {x ∷ xs}
          ∙ sym (M.─⊗─ .F-id)
          ∙ cong₂ M._⊗ₕ_ refl (sym (|rec| .F-id {xs})))

      opaque
        -- worst case scenario this is just a symmetric proof to ρ⟨⊗⟩
        η⟨⊗⟩ : ∀ x y →
          (M.α⟨ M.unit , x , y ⟩ M.⋆ (M.η⟨ x ⟩ M.⊗ₕ M.id {y}))
          ≡ M.η⟨ x M.⊗ y ⟩
        η⟨⊗⟩ x y = {!!}
        -- id⊗-cancel M
        --   ((cong₂ M._⊗ₕ_ ((sym (M.⋆IdR _))) refl ∙ M.─⊗─ .F-seq _ _)
        --   ∙ ⋆CancelL {C = M.C} (invIso (NatIsoAt M.α _))
        --     (sym (M.⋆Assoc _ _ _)
        --     ∙ cong₂ M._⋆_
        --         (sym (⋆InvLMove (NatIsoAt M.α _)
        --           (sym (M.⋆Assoc _ _ _)
        --           ∙ sym (⋆InvRMove (NatIsoAt M.α _) (⋆InvRMove
        --                                               (F-Iso {F = M.─⊗─} (CatIso× M.C M.C (NatIsoAt M.α _) idCatIso))
        --                                                 (M.⋆Assoc _ _ _ ∙ M.pentagon _ _ _ _)
        --                                                 ∙ M.⋆Assoc _ _ _)))))
        --         refl
        --     ∙ {!!}
        --     ∙ triangle' M _ _))

        μ-pf : ∀ xs ys zs →
          (M.α⟨ _ , _ , _ ⟩ M.⋆ (|μ| xs ys .fst M.⊗ₕ M.id)) M.⋆ |μ| (xs ++ ys) zs .fst
          ≡ ((M.id M.⊗ₕ |μ| ys zs .fst) M.⋆ |μ| xs (ys ++ zs) .fst) M.⋆ |rec| ⟪ L.α⟨ xs , ys , zs ⟩ ⟫
        μ-pf [] ys zs =
          (M.α⟨ _ , _ , _ ⟩ M.⋆ (M.η⟨ _ ⟩ M.⊗ₕ M.id)) M.⋆ |μ| ys zs .fst
            ≡⟨ cong₂ M._⋆_ (η⟨⊗⟩ (|rec| ⟅ ys ⟆) (|rec| ⟅ zs ⟆)) refl ⟩
          M.η⟨ _ ⟩ M.⋆ |μ| ys zs .fst
            ≡⟨ sym (M.η .trans .N-hom _) ⟩
          (M.id M.⊗ₕ |μ| ys zs .fst) M.⋆ M.η⟨ _ ⟩
            ≡⟨ sym (M.⋆IdR _) ∙ cong₂ M._⋆_ refl (sym (|rec| .F-id {ys ++ zs})) ⟩
          ((M.id M.⊗ₕ |μ| ys zs .fst) M.⋆ M.η⟨ _ ⟩) M.⋆ |rec| ⟪ L.id {ys ++ zs} ⟫
            ∎
        μ-pf (x ∷ xs) ys zs =
          (M.α⟨ _ , _ , _ ⟩ M.⋆ ((M.α⁻¹⟨ _ , _ , _ ⟩ M.⋆ (M.id M.⊗ₕ |μ| xs ys .fst)) M.⊗ₕ M.id))
            M.⋆ M.α⁻¹⟨ _ , _ , _ ⟩ M.⋆ (M.id M.⊗ₕ |μ| (xs ++ ys) zs .fst)
            ≡⟨ cong₂ M._⋆_ (cong₂ M._⋆_ refl (cong₂ M._⊗ₕ_ refl (sym (M.⋆IdL _)) ∙ M.─⊗─ .F-seq _ _) ∙ sym (M.⋆Assoc _ _ _)) refl ∙ M.⋆Assoc _ _ _ ∙ cong₂ M._⋆_ refl (sym (M.⋆Assoc _ _ _) ∙ cong₂ M._⋆_ (symNatIso M.α .trans .N-hom _) refl) ⟩
          (M.α⟨ _ , _ , _ ⟩ M.⋆ (M.α⁻¹⟨ _ , _ , _ ⟩ M.⊗ₕ M.id))
           M.⋆
           ((M.α⁻¹⟨ _ , _ , _ ⟩ M.⋆ (M.id M.⊗ₕ (|μ| xs ys .fst M.⊗ₕ M.id))) M.⋆ (M.id M.⊗ₕ |μ| (xs ++ ys) zs .fst))
            ≡⟨ {!cong₂ M._⋆_ ? ?!} ⟩
          ((M.id M.⊗ₕ |μ| ys zs .fst) M.⋆ (M.α⁻¹⟨ _ , _ , _ ⟩ M.⋆ (M.id M.⊗ₕ |μ| xs (ys ++ zs) .fst)))
           M.⋆ (M.id M.⊗ₕ |rec| ⟪ L.α⟨ xs , ys , zs ⟩ ⟫)
            ≡⟨ {!!} ⟩
          ((M.id M.⊗ₕ |μ| ys zs .fst) M.⋆ (M.α⁻¹⟨ _ , _ , _ ⟩ M.⋆ (M.id M.⊗ₕ |μ| xs (ys ++ zs) .fst))) M.⋆ |rec| ⟪ L.α⟨ x ∷ xs , ys , zs ⟩ ⟫
            ∎

        ρε-pf : ∀ xs →
          (|μ| xs [] .fst) M.⋆ (|rec| ⟪ L.ρ⟨ xs ⟩ ⟫) ≡ M.ρ⟨ |rec| ⟅ xs ⟆ ⟩
        -- famous property: ρ⟨ unit ⟩ ≡ η⟨ unit ⟩
        ρε-pf [] = cong₂ M._⋆_ refl (|rec| .F-id {x = []}) ∙ M.⋆IdR _
          ∙ sym (ρ⟨unit⟩≡η⟨unit⟩ M)
        ρε-pf (x ∷ xs) =
          cong₂ M._⋆_ refl (rec∷ L.ρ⟨ xs ⟩)
          ∙ M.⋆Assoc _ _ _
          ∙ cong₂ M._⋆_ refl (sym (M.─⊗─ .F-seq _ _)
          ∙ cong₂ M._⊗ₕ_ (M.⋆IdL _) (ρε-pf xs))
          ∙ cong₂ M._⋆_ refl (sym (ρ⟨⊗⟩ M) ) -- another famous Kelly lemma
          ∙ sym (M.⋆Assoc _ _ _)
          ∙ cong₂ M._⋆_ (M.α .nIso _ .sec) refl
          ∙ M.⋆IdL _

      rec : StrongMonoidalFunctor L M
      rec .F = |rec|
      rec .strmonstr .laxmonstr .ε = M.id
      rec .strmonstr .laxmonstr .μ .NatTrans.N-ob x = |μ| (x .fst) (x .snd) .fst
      rec .strmonstr .laxmonstr .μ .NatTrans.N-hom f = μ-nat (f .fst) (f .snd)
      rec .strmonstr .laxmonstr .αμ-law xs ys zs =
        {!!}
      rec .strmonstr .laxmonstr .ηε-law xs =
        cong₂ M._⋆_ (cong₂ M._⋆_ (M.─⊗─ .F-id) refl ∙ M.⋆IdL _) (|rec| .F-id {x = xs})
        ∙ M.⋆IdR _
      rec .strmonstr .laxmonstr .ρε-law xs =
        cong₂ M._⋆_ (cong₂ M._⋆_ (M.─⊗─ .F-id) refl ∙ M.⋆IdL _) refl ∙ ρε-pf xs
      rec .strmonstr .ε-isIso = idCatIso .snd
      rec .strmonstr .μ-isIso x = |μ| (x .fst) (x .snd) .snd

  -- private
  --   εL : FX.C [ FX.unit , |reflect| ⟅ [] ⟆ ]
  --   εL = FX.id

  --   -- TODO: make FreeMonoidalCategory opaque?
  --   |μL| : ∀ x y → FX.C [ (|reflect| ⟅ x ⟆) FX.⊗ (|reflect| ⟅ y ⟆) , |reflect| ⟅ x ++ y ⟆ ]
  --   |μL| = List.elim
  --     (λ y → FX.η⟨ |reflect| ⟅ y ⟆ ⟩)
  --     λ |μL| y → FX.α⁻¹⟨ _ , _ , _ ⟩ FX.⋆ (FX.id FX.⊗ₕ |μL| y)

  --   μL : FX.─⊗─ ∘F (|reflect| ×F |reflect|) ⇒ |reflect| ∘F L.─⊗─
  --   μL .NatTrans.N-ob = {!!}
  --   μL .NatTrans.N-hom = {!!}

  -- reflect : StrongMonoidalFunctor L FX
  -- reflect .StrongMonoidalFunctor.F = |reflect|
  -- reflect .StrongMonoidalFunctor.strmonstr .StrongMonoidalStr.laxmonstr .LaxMonoidalStr.ε = FX.id
  -- reflect .StrongMonoidalFunctor.strmonstr .StrongMonoidalStr.laxmonstr .LaxMonoidalStr.μ = {!!}
  -- reflect .StrongMonoidalFunctor.strmonstr .StrongMonoidalStr.laxmonstr .LaxMonoidalStr.αμ-law = {!!}
  -- reflect .StrongMonoidalFunctor.strmonstr .StrongMonoidalStr.laxmonstr .LaxMonoidalStr.ηε-law = {!!}
  -- reflect .StrongMonoidalFunctor.strmonstr .StrongMonoidalStr.laxmonstr .LaxMonoidalStr.ρε-law = {!!}
  -- reflect .StrongMonoidalFunctor.strmonstr .StrongMonoidalStr.ε-isIso = idCatIso .snd
  -- reflect .StrongMonoidalFunctor.strmonstr .StrongMonoidalStr.μ-isIso = {!!}
