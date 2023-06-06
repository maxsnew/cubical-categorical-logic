-- Free category generated from base objects and generators
-- This time not using a graph as the presentation of the generators
{-# OPTIONS --safe #-}

module Cubical.Categories.Constructions.Free.Category where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation
open import Cubical.Data.Sigma

private
  variable
    ℓc ℓc' ℓd ℓd' ℓg ℓg' ℓh ℓh' ℓj : Level

open Category
open Functor

record Quiver ℓg ℓg' : Type (ℓ-suc (ℓ-max ℓg ℓg')) where
  field
    ob : Type ℓg
    mor : Type ℓg'
    dom : mor → ob
    cod : mor → ob

open Quiver

record Interp (Q : Quiver ℓg ℓg') (𝓒 : Category ℓc ℓc')
              : Type (ℓ-max (ℓ-max ℓg ℓg') (ℓ-max ℓc ℓc')) where
  field
    I-ob : Q .ob → 𝓒 .ob
    I-hom : ∀ e → 𝓒 [ I-ob (Q .dom e) , I-ob (Q .cod e) ] 

open Interp

_∘I_ : {Q : Quiver ℓg ℓg'}{𝓒 : Category ℓc ℓc'}{𝓓 : Category ℓd ℓd'}
       (F : Functor 𝓒 𝓓) (ı : Interp Q 𝓒)
     → Interp Q 𝓓
(F ∘I ı) .I-ob x = F ⟅ ı .I-ob x ⟆
(F ∘I ı) .I-hom e = F ⟪ ı .I-hom e ⟫

module _ (Q : Quiver ℓg ℓg') where
  data Exp : Q .ob → Q .ob → Type (ℓ-max ℓg ℓg') where
    ↑_   : ∀ g → Exp (Q .dom g) (Q .cod g)
    idₑ  : ∀ {A} → Exp A A
    _⋆ₑ_ : ∀ {A B C} → (e : Exp A B) → (e' : Exp B C) → Exp A C
    ⋆ₑIdL : ∀ {A B} (e : Exp A B) → idₑ ⋆ₑ e ≡ e
    ⋆ₑIdR : ∀ {A B} (e : Exp A B) → e ⋆ₑ idₑ ≡ e
    ⋆ₑAssoc : ∀ {A B C D} (e : Exp A B)(f : Exp B C)(g : Exp C D)
            → (e ⋆ₑ f) ⋆ₑ g ≡ e ⋆ₑ (f ⋆ₑ g)
    isSetExp : ∀ {A B} → isSet (Exp A B)
    
  FreeCat : Category _ _
  FreeCat .ob = Q .ob
  FreeCat .Hom[_,_] = Exp
  FreeCat .id = idₑ
  FreeCat ._⋆_ = _⋆ₑ_
  FreeCat .⋆IdL = ⋆ₑIdL
  FreeCat .⋆IdR = ⋆ₑIdR
  FreeCat .⋆Assoc = ⋆ₑAssoc
  FreeCat .isSetHom = isSetExp

  η : Interp Q FreeCat
  η .I-ob = λ x → x
  η .I-hom = ↑_

  module _ {ℓc ℓc'} {𝓒 : Category ℓc ℓc'} (F F' : Functor FreeCat 𝓒) where
    module _ (agree-on-η : F ∘I η ≡ F' ∘I η)
              where
        private
          aoo : ∀ c → F ⟅ c ⟆ ≡ F' ⟅ c ⟆
          aoo = (λ c i → agree-on-η i .I-ob c)

          aom-t : ∀ {c c'} (e : Exp c c') → Type _
          aom-t {c}{c'} e = PathP (λ i → 𝓒 [ aoo c i , aoo c' i ]) (F ⟪ e ⟫) (F' ⟪ e ⟫)

          aom-id : ∀ {c} → aom-t (idₑ {c})
          aom-id = F .F-id ◁ (λ i → 𝓒 .id) ▷ sym (F' .F-id)

          aom-seq : ∀ {c c' c''} (e : Exp c c')(e' : Exp c' c'') → aom-t e → aom-t e' → aom-t (e ⋆ₑ e')
          aom-seq e e' ihe ihe' = F .F-seq e e' ◁ (λ i → ihe i ⋆⟨ 𝓒 ⟩ ihe' i) ▷ sym (F' .F-seq e e')

          aom : ∀ {c c'} (e : Exp c c') → aom-t e
          aom (↑ x) = λ i → agree-on-η i .I-hom x
          aom idₑ = aom-id
          aom (e ⋆ₑ e') = aom-seq e e' (aom e) (aom e')
          aom (⋆ₑIdL e i) = isSet→SquareP (λ i j → 𝓒 .isSetHom) (aom-seq idₑ e aom-id (aom e)) (aom e) (λ i → F ⟪ ⋆ₑIdL e i ⟫) ((λ i → F' ⟪ ⋆ₑIdL e i ⟫)) i
          aom (⋆ₑIdR e i) = isSet→SquareP (λ i j → 𝓒 .isSetHom) (aom-seq e idₑ (aom e) aom-id) (aom e) (λ i → F ⟪ ⋆ₑIdR e i ⟫) ((λ i → F' ⟪ ⋆ₑIdR e i ⟫)) i
          aom (⋆ₑAssoc e e' e'' i) = isSet→SquareP (λ _ _ → 𝓒 .isSetHom) (aom-seq _ _ (aom-seq _ _ (aom e) (aom e')) (aom e'')) (aom-seq _ _ (aom e) (aom-seq _ _ (aom e') (aom e''))) ((λ i → F ⟪ ⋆ₑAssoc e e' e'' i ⟫)) (λ i → F' ⟪ ⋆ₑAssoc e e' e'' i ⟫) i
          aom (isSetExp e e' x y i j) = isSet→SquareP {A = λ i j → aom-t (isSetExp e e' x y i j)} (λ i j → isOfHLevelPathP 2 (𝓒 .isSetHom) (F ⟪ isSetExp e e' x y i j ⟫) (F' ⟪ isSetExp e e' x y i j ⟫)) (λ j → aom (x j)) (λ j → aom (y j)) (λ i → aom e) (λ i → aom e') i j

        ind : F ≡ F'
        ind = Functor≡ aoo aom
  module _ (𝓒 : Category ℓc ℓc') (ı : Interp Q 𝓒) where
    recF : ∀ {A B} → Exp A B → 𝓒 [ ı .I-ob A , ı .I-ob B ]
    recF (↑ g) = ı .I-hom g
    recF idₑ = 𝓒 .id
    recF (e ⋆ₑ e') = recF e ⋆⟨ 𝓒 ⟩ recF e'
    recF (⋆ₑIdL e i) = 𝓒 .⋆IdL (recF e) i
    recF (⋆ₑIdR e i) = 𝓒 .⋆IdR (recF e) i
    recF (⋆ₑAssoc e e' e'' i) = 𝓒 .⋆Assoc (recF e) (recF e') (recF e'') i
    recF (isSetExp e e' p q i j) =
      𝓒 .isSetHom (recF e) (recF e') (cong recF p) (cong recF q) i j

    rec : Functor FreeCat 𝓒
    rec .F-ob v = ı .I-ob v
    rec .F-hom = recF
    rec .F-id = refl
    rec .F-seq e e' = refl

    module RecLemmas where
      rec-extends-ı : (rec ∘I η) ≡ ı
      rec-extends-ı = refl

      rec-uniq : ∀ {F : Functor FreeCat 𝓒} → (F ∘I η) ≡ ı → F ≡ rec
      rec-uniq {F} aog = ind F rec aog

      rec-contr : ∃![ F ∈ Functor FreeCat 𝓒 ] F ∘I η ≡ ı
      rec-contr .fst = rec , refl
      rec-contr .snd y =
        ΣPathP ( (sym (rec-uniq (y .snd)))
               , (λ i j → y .snd ((~ i) ∨ j)))
