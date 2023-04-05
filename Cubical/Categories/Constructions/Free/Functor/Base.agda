-- Free functor between categories generated from two graphs and a homomorphism between them
{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Constructions.Free.Functor.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function renaming (_∘_ to _∘f_)
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation.Base hiding (_⟦_⟧)
open import Cubical.Data.Graph.Base
open import Cubical.Data.Sigma

open import Cubical.Data.Graph.Properties
open import Cubical.Data.Empty
open import Cubical.Categories.Constructions.Free.General as Free hiding (module Semantics)
open import Cubical.Categories.Constructions.Free.UnderlyingGraph

open import Cubical.Tactics.CategorySolver.Reflection

private
  variable
    ℓc ℓc' ℓd ℓd' ℓg ℓg' ℓh ℓh' : Level

open Category
open Functor
open NatTrans
open NatIso
open isIso


module _ (G : Graph ℓg ℓg') (H : Graph ℓh ℓh') (ϕ : GraphHom G H) where
  data FExp : H .Node → H .Node → Type (((ℓ-max ℓg (ℓ-max ℓg' (ℓ-max ℓh ℓh'))))) where
    -- free category on H
    ↑f_ : ∀ {A B} → H .Edge A B → FExp A B
    idf : ∀ {A} → FExp A A
    _⋆f_ : ∀ {A B C} → FExp A B → FExp B C → FExp A C
    ⋆fIdL : ∀ {A B} (e : FExp A B) → idf ⋆f e ≡ e
    ⋆fIdR : ∀ {A B} (e : FExp A B) → e ⋆f idf ≡ e
    ⋆fAssoc : ∀ {A B C D} (e : FExp A B)(f : FExp B C)(g : FExp C D)
            → (e ⋆f f) ⋆f g ≡ e ⋆f (f ⋆f g)
    isSetFExp : ∀ {A B} → isSet (FExp A B)

    -- that also freely adds in a functor from the free category on G
    F⟪_⟫ : ∀ {A B} → Exp G A B → FExp (ϕ $g A) (ϕ $g B)
    F-idₑ : ∀ {A} → F⟪ idₑ {A = A} ⟫ ≡ idf
    F-seqₑ : ∀ {A B C} (f : Exp G A B)(g : Exp G B C) → F⟪ f ⋆ₑ g ⟫ ≡ (F⟪ f ⟫ ⋆f F⟪ g ⟫)

    -- that agrees with ϕ on generators
    F⟪⟫-ϕ-agree : ∀ {A B} → (e : G .Edge A B) → F⟪ ↑ e ⟫ ≡ ↑f (ϕ <$g> e)

  FreeH+ϕ : Category _ _
  FreeH+ϕ .ob = H .Node
  FreeH+ϕ .Hom[_,_] = FExp
  FreeH+ϕ .id = idf
  FreeH+ϕ ._⋆_ = _⋆f_
  FreeH+ϕ .⋆IdL = ⋆fIdL
  FreeH+ϕ .⋆IdR = ⋆fIdR
  FreeH+ϕ .⋆Assoc = ⋆fAssoc
  FreeH+ϕ .isSetHom = isSetFExp

  FreeG = FreeCat G

  Freeϕ : Functor FreeG FreeH+ϕ
  Freeϕ = Free.Semantics.sem G FreeH+ϕ homo where
    homo : GraphHom G (Ugr FreeH+ϕ)
    homo ._$g_ = _$g_ ϕ
    homo ._<$g>_ = λ z → F⟪ ↑ z ⟫

  -- The universal interpretation
  ηG : Interp G FreeG
  ηG = η G

  ηH : Interp H FreeH+ϕ
  ηH $g x = x
  ηH <$g> x = ↑f x

  ηϕ : InterpIso G FreeH+ϕ (ηG ⋆Interp Freeϕ) (ϕ ⋆GrHom ηH)
  ηϕ .fst .fst v = FreeH+ϕ .id
  ηϕ .fst .snd e = FreeH+ϕ .⋆IdR _ ∙ F⟪⟫-ϕ-agree _ ∙ sym (FreeH+ϕ .⋆IdL _)
  ηϕ .snd v = idCatIso .snd

  module Semantics {𝓒 : Category ℓc ℓc'}{𝓓 : Category ℓd ℓd'}(𝓕 : Functor 𝓒 𝓓)
                   (ıG : GraphHom G (Ugr 𝓒))
                   (ıH : GraphHom H (Ugr 𝓓))
                   (ıϕ : InterpIso G 𝓓 (ıG ⋆GrHom Uhom 𝓕) (ϕ ⋆GrHom ıH))
                   where
     sem𝓒 = Free.Semantics.sem G 𝓒 ıG
     sem𝓒-extends-ıG : (ηG ⋆Interp sem𝓒) ≡ ıG
     sem𝓒-extends-ıG = refl

     ⟦_⟧ : ∀ {A B} → FExp A B → 𝓓 [ ıH $g A , ıH $g B ]
     -- first the data
     ⟦ ↑f x ⟧ = ıH <$g> x
     ⟦ idf ⟧ = 𝓓 .id
     ⟦ f ⋆f f₁ ⟧ = ⟦ f ⟧ ⋆⟨ 𝓓 ⟩ ⟦ f₁ ⟧
     ⟦ F⟪_⟫ {A}{B} x ⟧ = ıϕ .snd A .inv ⋆⟨ 𝓓 ⟩ 𝓕 ⟪ sem𝓒 ⟪ x ⟫ ⟫ ⋆⟨ 𝓓 ⟩ ıϕ .fst .fst B -- ϕ≅ .trans .N-ob B
     -- then the equalities
     ⟦ ⋆fIdL f i ⟧ = 𝓓 .⋆IdL ⟦ f ⟧ i
     ⟦ ⋆fIdR f i ⟧ = 𝓓 .⋆IdR ⟦ f ⟧ i
     ⟦ ⋆fAssoc f f₁ f₂ i ⟧ = 𝓓 .⋆Assoc ⟦ f ⟧ ⟦ f₁ ⟧ ⟦ f₂ ⟧ i
     -- apologies
     ⟦ F-idₑ {A} i ⟧ =
       ((λ i →
         ((λ i → ıϕ .snd A .inv ⋆⟨ 𝓓 ⟩ (𝓕 ∘F sem𝓒) .F-id i) ∙ 𝓓 .⋆IdR _) i
         ⋆⟨ 𝓓 ⟩ (ıϕ .fst .fst A))
         ∙ ıϕ .snd A .sec) i
     ⟦ F-seqₑ {A}{B}{C} f g i ⟧ =
       (seq' 𝓓 (seq' 𝓓 (ıϕ .snd A .inv) (𝓕 ⟪ sem𝓒 ⟪ f ⋆ₑ g ⟫ ⟫)) (ıϕ .fst .fst C)
          ≡[ i ]⟨ seq' 𝓓 (seq' 𝓓 (ıϕ .snd A .inv) (funcComp 𝓕 sem𝓒 .F-seq f g i)) (ıϕ .fst .fst C) ⟩
        seq' 𝓓 (seq' 𝓓 (ıϕ .snd A .inv) (𝓕 ⟪ sem𝓒 ⟪ f ⟫ ⟫ ⋆⟨ 𝓓 ⟩ 𝓕 ⟪ sem𝓒 ⟪ g ⟫ ⟫)) (ıϕ .fst .fst C)
          ≡⟨ solveCat! 𝓓 ⟩
        (seq' 𝓓 (ıϕ .snd A .inv) (𝓕 ⟪ sem𝓒 ⟪ f ⟫ ⟫)) ⋆⟨ 𝓓 ⟩ 𝓓 .id ⋆⟨ 𝓓 ⟩ 𝓕 ⟪ sem𝓒 ⟪ g ⟫ ⟫ ⋆⟨ 𝓓 ⟩ (ıϕ .fst .fst C)
          ≡[ i ]⟨ (seq' 𝓓 (ıϕ .snd A .inv) (𝓕 ⟪ sem𝓒 ⟪ f ⟫ ⟫)) ⋆⟨ 𝓓 ⟩ ıϕ .snd B .ret (~ i) ⋆⟨ 𝓓 ⟩ 𝓕 ⟪ sem𝓒 ⟪ g ⟫ ⟫ ⋆⟨ 𝓓 ⟩ (ıϕ .fst .fst C) ⟩
        (seq' 𝓓 (ıϕ .snd A .inv) (𝓕 ⟪ sem𝓒 ⟪ f ⟫ ⟫)) ⋆⟨ 𝓓 ⟩ (ıϕ .fst .fst B ⋆⟨ 𝓓 ⟩ ıϕ .snd B .inv) ⋆⟨ 𝓓 ⟩ 𝓕 ⟪ sem𝓒 ⟪ g ⟫ ⟫ ⋆⟨ 𝓓 ⟩ (ıϕ .fst .fst C)
          ≡⟨ solveCat! 𝓓 ⟩
        seq' 𝓓 (seq' 𝓓 (seq' 𝓓 (ıϕ .snd A .inv) (𝓕 ⟪ sem𝓒 ⟪ f ⟫ ⟫)) (ıϕ .fst .fst B)) (seq' 𝓓 (seq' 𝓓 (ıϕ .snd B .inv) (𝓕 ⟪ sem𝓒 ⟪ g ⟫ ⟫)) (ıϕ .fst .fst C)) ∎
       ) i
     ⟦ F⟪⟫-ϕ-agree {A}{B} e i ⟧ =
       (ıϕ .snd A .inv ⋆⟨ 𝓓 ⟩ 𝓕 ⟪ sem𝓒 ⟪ ↑ e ⟫ ⟫ ⋆⟨ 𝓓 ⟩ ıϕ .fst .fst B
          ≡[ i ]⟨ InterpReasoning.sqLL _ _ _ _ ıϕ {e = e} (~ i) ⋆⟨ 𝓓 ⟩ ıϕ .fst .fst B ⟩
         ıH <$g> (ϕ <$g> e) ⋆⟨ 𝓓 ⟩ ıϕ .snd B .inv ⋆⟨ 𝓓 ⟩ ıϕ .fst .fst B
          ≡⟨ 𝓓 .⋆Assoc _ _ _ ⟩
         ıH <$g> (ϕ <$g> e) ⋆⟨ 𝓓 ⟩ (ıϕ .snd B .inv ⋆⟨ 𝓓 ⟩ ıϕ .fst .fst B)
          ≡⟨ (λ i → (ıH <$g> (ϕ <$g> e)) ⋆⟨ 𝓓 ⟩ ıϕ .snd B .sec i) ⟩
         ıH <$g> (ϕ <$g> e) ⋆⟨ 𝓓 ⟩ 𝓓 .id
          ≡⟨ 𝓓 .⋆IdR _ ⟩
        ıH <$g> (ϕ <$g> e) ∎
       ) i
     -- then the 2-cells
     ⟦ isSetFExp f f₁ x y i j ⟧ = 𝓓 .isSetHom ⟦ f ⟧ ⟦ f₁ ⟧ (cong ⟦_⟧ x) (cong ⟦_⟧ y) i j

     sem𝓓 : Functor FreeH+ϕ 𝓓
     sem𝓓 .F-ob x = ıH $g x
     sem𝓓 .F-hom = ⟦_⟧   
     sem𝓓 .F-id = refl   
     sem𝓓 .F-seq f g = refl

     sem𝓓-extends-ıH : (ηH ⋆Interp sem𝓓) ≡ ıH
     sem𝓓-extends-ıH = refl

     semF : NatIso (𝓕 ∘F sem𝓒) (sem𝓓 ∘F Freeϕ)
     semF = uniqueness-principle G (𝓕 ∘F sem𝓒) (sem𝓓 ∘F Freeϕ)
       (seqInterpIso ıϕ (symInterpIso (sem𝓓 ⊙ʳInterp ηϕ)))

     semF-extends-ıϕ : seqInterpIso (semF ⊙ˡInterp ηG) (sem𝓓 ⊙ʳInterp ηϕ) ≡ ıϕ
     semF-extends-ıϕ =
       seqInterpIso (semF ⊙ˡInterp ηG) (sem𝓓 ⊙ʳInterp ηϕ)
         ≡[ i ]⟨ seqInterpIso (uniqueness-principle-restricts _ _ (sem𝓓 ∘F Freeϕ) ((seqInterpIso ıϕ (symInterpIso (sem𝓓 ⊙ʳInterp ηϕ)))) i) (sem𝓓 ⊙ʳInterp ηϕ) ⟩
       seqInterpIso (seqInterpIso ıϕ (symInterpIso (sem𝓓 ⊙ʳInterp ηϕ))) (sem𝓓 ⊙ʳInterp ηϕ)
         ≡⟨ seqInterpIsoAssoc _ _ _ ∙ cong (seqInterpIso ıϕ) (symInterpIsoInvl _) ∙ seqInterpIsoId _ ⟩
       ıϕ ∎

