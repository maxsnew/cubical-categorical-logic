-- Free category over a directed graph/quiver
-- This time without any assumptions on the HLevels of the graph
{-# OPTIONS --safe #-}

module Cubical.Categories.Constructions.Free.General where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation.Base hiding (_⟦_⟧)
open import Cubical.Data.Graph.Base

open import Cubical.Data.Graph.Properties

private
  variable
    ℓc ℓc' ℓd ℓd' ℓg ℓg' : Level

open Category
open Functor

-- Underlying graph of a category
Ugr : ∀ {ℓc ℓc'} (𝓒 : Category ℓc ℓc') → Graph ℓc ℓc'
Ugr 𝓒 .Node = 𝓒 .ob
Ugr 𝓒 .Edge = 𝓒 .Hom[_,_]

Uhom : ∀ {ℓc ℓc' ℓd ℓd'} {𝓒 : Category ℓc ℓc'} {𝓓 : Category ℓd ℓd'} (F : Functor 𝓒 𝓓)
     → GraphHom (Ugr 𝓒) (Ugr 𝓓)
Uhom F ._$g_ = Functor.F-ob F
Uhom F ._<$g>_ = Functor.F-hom F

module _ (G : Graph ℓg ℓg') (𝓒 : Category ℓc ℓc') where
  Interp : Type _
  Interp = GraphHom G (Ugr 𝓒)

  InterpTrans : Interp → Interp → Type _
  InterpTrans ı ı' =
    Σ[ f ∈ (∀ v → 𝓒 [ ı $g v , ı' $g v ])]
    (∀ {v}{w}(e : G .Edge v w) → f w ∘⟨ 𝓒 ⟩ (ı <$g> e) ≡ ı' <$g> e ∘⟨ 𝓒 ⟩ f v)

  isInterpIso : { ı ı' : Interp} → InterpTrans ı ı' → Type (ℓ-max ℓg ℓc')
  isInterpIso α = ∀ v → isIso 𝓒 (α .fst v)

  InterpIso : Interp → Interp → Type _
  InterpIso ı ı' = Σ (InterpTrans ı ı') isInterpIso

  -- if 𝓒 is univalent, interpIso should be equivalent to identity

module _ (G : Graph ℓg ℓg') where
    -- "Category expressions"
    data Exp : G .Node → G .Node → Type (ℓ-max ℓg ℓg') where
      ↑_   : ∀ {A B} → G .Edge A B → Exp A B
      idₑ  : ∀ {A} → Exp A A
      _⋆ₑ_ : ∀ {A B C} → Exp A B → Exp B C → Exp A C
      ⋆ₑIdL : ∀ {A B} (e : Exp A B) → idₑ ⋆ₑ e ≡ e
      ⋆ₑIdR : ∀ {A B} (e : Exp A B) → e ⋆ₑ idₑ ≡ e
      ⋆ₑAssoc : ∀ {A B C D} (e : Exp A B)(f : Exp B C)(g : Exp C D)
              → (e ⋆ₑ f) ⋆ₑ g ≡ e ⋆ₑ (f ⋆ₑ g)
      isSetExp : ∀ {A B} → isSet (Exp A B)

    FreeCat : Category ℓg (ℓ-max ℓg ℓg')
    FreeCat .ob = G .Node
    FreeCat .Hom[_,_] = Exp
    FreeCat .id = idₑ
    FreeCat ._⋆_ = _⋆ₑ_
    FreeCat .⋆IdL = ⋆ₑIdL
    FreeCat .⋆IdR = ⋆ₑIdR
    FreeCat .⋆Assoc = ⋆ₑAssoc
    FreeCat .isSetHom = isSetExp

    η : Interp G FreeCat
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

      sem-extends-ı : η ⋆GrHom Uhom sem ≡ ı
      sem-extends-ı i ._$g_ x = ı  $g  x
      sem-extends-ı i <$g> x  = ı <$g> x

      module _ (F : Functor FreeCat 𝓒) (α : InterpIso G 𝓒 (η ⋆GrHom Uhom F) ı) where
        open NatIso
        open NatTrans
        αMorphisms = α .fst .fst
        αNat = α .fst .snd

        private
          semITINId : ∀ {v}
                    → F ⟪ idₑ ⟫ ⋆⟨ 𝓒 ⟩ αMorphisms v ≡ αMorphisms v ⋆⟨ 𝓒 ⟩ 𝓒 .id
          semITINId =
            F ⟪ idₑ ⟫ ⋆⟨ 𝓒 ⟩ αMorphisms _ ≡[ i ]⟨ F .F-id i ⋆⟨ 𝓒 ⟩ αMorphisms _ ⟩
            𝓒 .id ⋆⟨ 𝓒 ⟩ αMorphisms _ ≡⟨ 𝓒 .⋆IdL (αMorphisms _) ∙ sym (𝓒 .⋆IdR (αMorphisms _)) ⟩
            αMorphisms _ ⋆⟨ 𝓒 ⟩ 𝓒 .id ∎
          semITIN⋆ : ∀ {u}{v}{w} → (e : FreeCat [ u , v ])(e' : FreeCat [ v , w ])
                   → F ⟪ e ⟫ ⋆⟨ 𝓒 ⟩ αMorphisms _ ≡ αMorphisms _ ⋆⟨ 𝓒 ⟩ ⟦ e ⟧
                   → F ⟪ e' ⟫ ⋆⟨ 𝓒 ⟩ αMorphisms _ ≡ αMorphisms _ ⋆⟨ 𝓒 ⟩ ⟦ e' ⟧
                   → F ⟪ e ⋆ₑ e' ⟫ ⋆⟨ 𝓒 ⟩ αMorphisms _ ≡ αMorphisms _ ⋆⟨ 𝓒 ⟩ (⟦ e ⟧ ⋆⟨ 𝓒 ⟩ ⟦ e' ⟧)
          semITIN⋆ e e' ih ih' =
            F ⟪ e ⋆ₑ e' ⟫ ⋆⟨ 𝓒 ⟩ αMorphisms _ ≡[ i ]⟨ F .F-seq e e' i ⋆⟨ 𝓒 ⟩ αMorphisms _ ⟩
            (F ⟪ e ⟫ ⋆⟨ 𝓒 ⟩ F ⟪ e' ⟫) ⋆⟨ 𝓒 ⟩ αMorphisms _ ≡⟨ (𝓒 .⋆Assoc (F ⟪ e ⟫) (F ⟪ e' ⟫) (αMorphisms _)) ⟩
            F ⟪ e ⟫ ⋆⟨ 𝓒 ⟩ (F ⟪ e' ⟫ ⋆⟨ 𝓒 ⟩ αMorphisms _) ≡[ i ]⟨ F ⟪ e ⟫ ⋆⟨ 𝓒 ⟩ ih' i ⟩
            F ⟪ e ⟫ ⋆⟨ 𝓒 ⟩ (αMorphisms _ ⋆⟨ 𝓒 ⟩ ⟦ e' ⟧) ≡⟨ sym (𝓒 .⋆Assoc (F ⟪ e ⟫) (αMorphisms _) ⟦ e' ⟧) ⟩
            (F ⟪ e ⟫ ⋆⟨ 𝓒 ⟩ αMorphisms _) ⋆⟨ 𝓒 ⟩ ⟦ e' ⟧ ≡[ i ]⟨ ih i ⋆⟨ 𝓒 ⟩ ⟦ e' ⟧ ⟩
            (αMorphisms _ ⋆⟨ 𝓒 ⟩ ⟦ e ⟧) ⋆⟨ 𝓒 ⟩ ⟦ e' ⟧ ≡⟨ 𝓒 .⋆Assoc (αMorphisms _) ⟦ e ⟧ ⟦ e' ⟧ ⟩
            αMorphisms _ ⋆⟨ 𝓒 ⟩ (⟦ e ⟧ ⋆⟨ 𝓒 ⟩ ⟦ e' ⟧) ∎


        semITransIsNat : ∀ {v w} → (e : FreeCat [ v , w ])
                       → F ⟪ e ⟫ ⋆⟨ 𝓒 ⟩ αMorphisms w ≡ αMorphisms v ⋆⟨ 𝓒 ⟩ ⟦ e ⟧
        semITransIsNat {v} {w} (↑ f) = αNat f
        semITransIsNat {v} {.v} idₑ = semITINId
        semITransIsNat {v} {w} (e ⋆ₑ e') = semITIN⋆ e e' (semITransIsNat e) (semITransIsNat e')

        semITransIsNat {v} {w} (⋆ₑIdL e i) =
          isSet→SquareP (λ _ _ → 𝓒 .isSetHom)
                        (semITIN⋆ idₑ e semITINId (semITransIsNat e))
                        (semITransIsNat e)
                        (λ i → (F ⟪ ⋆ₑIdL e i ⟫) ⋆⟨ 𝓒 ⟩ αMorphisms _)
                        (λ i → αMorphisms _ ⋆⟨ 𝓒 ⟩ 𝓒 .⋆IdL ⟦ e ⟧ i) i
        semITransIsNat {v} {w} (⋆ₑIdR e i) =
          isSet→SquareP (λ _ _ → 𝓒 .isSetHom)
                        (semITIN⋆ e idₑ (semITransIsNat e) semITINId)
                        (semITransIsNat e)
                        (λ i → 𝓒 ._⋆_ (F ⟪ ⋆ₑIdR e i ⟫) (αMorphisms _))
                        (λ i → seq' 𝓒 (αMorphisms _) (𝓒 .⋆IdR ⟦ e ⟧ i))
                        i
        semITransIsNat {v} {w} (⋆ₑAssoc e e' e'' i) =
          isSet→SquareP (λ _ _ → 𝓒 .isSetHom)
                        (semITIN⋆ (e ⋆ₑ e') e'' (semITIN⋆ e e' (semITransIsNat e) (semITransIsNat e')) (semITransIsNat e''))
                        (semITIN⋆ e (e' ⋆ₑ e'') (semITransIsNat e) (semITIN⋆ e' e'' (semITransIsNat e') (semITransIsNat e'')))
                        (λ i → seq' 𝓒 (F ⟪ ⋆ₑAssoc e e' e'' i ⟫) (αMorphisms w))
                        (λ i → seq' 𝓒 (αMorphisms v) (𝓒 .⋆Assoc ⟦ e ⟧ ⟦ e' ⟧ ⟦ e'' ⟧ i))
                        i
        semITransIsNat {v} {w} (isSetExp e e' p q i j) =
          isSet→SquareP (λ i j → isSet→isGroupoid (𝓒 .isSetHom)
                                                  ((F ⟪ isSetExp e e' p q i j ⟫) ⋆⟨ 𝓒 ⟩ (αMorphisms w))
                                                  (αMorphisms v ⋆⟨ 𝓒 ⟩ ⟦ isSetExp e e' p q i j ⟧))
                        (λ j → semITransIsNat (p j))
                        (λ j → semITransIsNat (q j))
                        (λ i → semITransIsNat e)
                        (λ i → semITransIsNat e')
                        i
                        j

        semIIso : NatIso F sem
        semIIso .trans .N-ob = αMorphisms
        semIIso .trans .N-hom = semITransIsNat
        semIIso .nIso = α .snd

        -- TODO: prove semIIso restricts to α and it's the unique such natIso
-- co-unit of the 2-adjunction
ϵ : ∀ {𝓒 : Category ℓc ℓc'} → Functor (FreeCat (Ugr 𝓒)) 𝓒
ϵ {𝓒 = 𝓒} = Semantics.sem (Ugr 𝓒) 𝓒 (Uhom {𝓓 = 𝓒} Id)
