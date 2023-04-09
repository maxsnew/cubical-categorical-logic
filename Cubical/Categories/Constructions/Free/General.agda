-- Free category over a directed graph/quiver
-- This time without any assumptions on the HLevels of the graph
{-# OPTIONS --safe --lossy-unification #-}

module Cubical.Categories.Constructions.Free.General where

open import Cubical.Categories.Morphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation hiding (_⟦_⟧)
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Data.Graph.Base

open import Cubical.Data.Graph.Properties
open import Cubical.Categories.Constructions.Free.UnderlyingGraph

private
  variable
    ℓc ℓc' ℓd ℓd' ℓg ℓg' : Level

open Category
open Functor
open NatIso hiding (sqRL; sqLL)
open NatTrans

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

      sem-extends-ı : (η ⋆Interp sem) ≡ ı
      sem-extends-ı = refl

      module _ (F : Functor FreeCat 𝓒) (α : InterpIso G 𝓒 (η ⋆GrHom Uhom F) ı) where
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

        semII-restricts-to-α : semIIso ⊙ˡInterp η ≡ α
        semII-restricts-to-α = refl
        -- TODO: prove semIIso is the unique such natIso

    module _ {𝓒 : Category ℓc ℓc'}{𝓓 : Category ℓd ℓd'}
             (ı : Interp G 𝓒)
             (F : Functor 𝓒 𝓓)
             where
      sem-is-natural : NatIso (F ∘F Semantics.sem 𝓒 ı) (Semantics.sem 𝓓 (F ∘Interp ı))
      sem-is-natural = Semantics.semIIso _ (F ∘Interp ı) (F ∘F Semantics.sem _ ı) (idInterpIso G _)

      sem-is-natural-restricts : sem-is-natural ⊙ˡInterp η ≡ idInterpIso G 𝓓
      sem-is-natural-restricts = Semantics.semII-restricts-to-α _ (F ∘Interp ı) (F ∘F Semantics.sem _ ı) (idInterpIso G _)

    uniqueness-principle : ∀ {𝓒 : Category ℓc ℓc'} →
                           (F : Functor FreeCat 𝓒) →
                           (F' : Functor FreeCat 𝓒) →
                           (agree-on-generators : InterpIso _ 𝓒 (η ⋆Interp F) (η ⋆Interp F')) →
                           NatIso F F'
    uniqueness-principle {𝓒 = 𝓒} F F' agree-on-generators =
      seqNatIso (Semantics.semIIso 𝓒 (η ⋆Interp F') F agree-on-generators)
      (symNatIso (Semantics.semIIso 𝓒 (η ⋆Interp F') F' (idInterpIso G 𝓒)))

    uniqueness-principle-restricts : ∀ {𝓒 : Category ℓc ℓc'} →
                           (F : Functor FreeCat 𝓒) →
                           (F' : Functor FreeCat 𝓒) →
                           (agree-on-generators : InterpIso _ 𝓒 (η ⋆Interp F) (η ⋆Interp F')) →
                           uniqueness-principle F F' agree-on-generators ⊙ˡInterp η ≡ agree-on-generators
    uniqueness-principle-restricts F F' agree =
      uniqueness-principle F F' agree ⊙ˡInterp η
        ≡⟨ ⊙ˡInterp-Seq ((Semantics.semIIso _ (η ⋆Interp F') F agree)) ((symNatIso (Semantics.semIIso _ (η ⋆Interp F') F' (idInterpIso _ _)))) η ⟩
      seqInterpIso ((Semantics.semIIso _ (η ⋆Interp F') F agree) ⊙ˡInterp η)
                   ((symNatIso (Semantics.semIIso _ (η ⋆Interp F') F' (idInterpIso _ _))) ⊙ˡInterp η)
        ≡⟨ cong₂ seqInterpIso (Semantics.semII-restricts-to-α _ (η ⋆Interp F') F agree) lemma ⟩
      seqInterpIso agree (idInterpIso _ _)
        ≡⟨ seqInterpIsoIdR agree ⟩
      agree ∎
      where
        lemma : (symNatIso (Semantics.semIIso _ (η ⋆Interp F') F' (idInterpIso G _)) ⊙ˡInterp η)
                ≡ idInterpIso G _
        lemma = ⊙ˡInterp-Sym ((Semantics.semIIso _ (η ⋆Interp F') F' (idInterpIso G _))) η
                ∙ cong symInterpIso (Semantics.semII-restricts-to-α _ (η ⋆Interp F') F' ((idInterpIso G _)))
                ∙ symInterpIsoId


-- co-unit of the 2-adjunction
ϵ : ∀ {𝓒 : Category ℓc ℓc'} → Functor (FreeCat (Ugr 𝓒)) 𝓒
ϵ {𝓒 = 𝓒} = Semantics.sem (Ugr 𝓒) 𝓒 (Uhom {𝓓 = 𝓒} Id)
