{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Tactics.FunctorSolver.Solver where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Data.Graph.Base
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Instances.Sets

open import Cubical.Categories.Constructions.Free.General as FreeCat
open import Cubical.Categories.Constructions.Free.Functor as FreeFunctor
open import Cubical.Categories.Constructions.Free.UnderlyingGraph
open import Cubical.Data.Graph.Properties
open import Cubical.Categories.Yoneda.More
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Tactics.CategorySolver.Reflection

private
  variable
    ℓc ℓc' ℓd ℓd' ℓb ℓb' : Level
open Category
open Functor
open NatIso
open NatTrans

module Eval (𝓒 : Category ℓc ℓc') (𝓓 : Category ℓd ℓd')  (𝓕 : Functor 𝓒 𝓓) where
  -- category of 𝓒 expressions
  Free𝓒 = FreeG (Ugr 𝓒) (Ugr 𝓓) (Uhom 𝓕)
  Free𝓓 = FreeH+ϕ (Ugr 𝓒) (Ugr 𝓓) (Uhom 𝓕)
  Free𝓕 = Freeϕ (Ugr 𝓒) (Ugr 𝓓) (Uhom 𝓕)
  𝓟𝓓 = PresheafCategory 𝓓 ℓd'

  module TautoSem = FreeFunctor.Semantics (Ugr 𝓒) (Ugr 𝓓) (Uhom 𝓕) 𝓕 (Uhom Id) (Uhom Id) (idInterpIso _ _)

  module YoSem = FreeFunctor.Semantics (Ugr 𝓒) (Ugr 𝓓) (Uhom 𝓕) (Id {C = 𝓟𝓓}) (Uhom (YONEDA ∘F 𝓕)) (Uhom YONEDA) (idInterpIso _ _)

  eval : ∀ {A B} → Free𝓓 [ A , B ] → 𝓓 [ A , B ]
  eval {A}{B} e = Iso.fun (yonedaᴾ {C = 𝓓} (𝓓 [-, B ]) A) (YoSem.sem𝓓 ⟪ e ⟫)

  YoTauto-Yo-Agree : NatIso (YONEDA ∘F TautoSem.sem𝓓) YoSem.sem𝓓
  YoTauto-Yo-Agree =
    sem𝓓-iso (Ugr 𝓒) (Ugr 𝓓) (Uhom 𝓕) (Id {C = 𝓟𝓓}) (Uhom (YONEDA ∘F 𝓕)) (Uhom YONEDA) (idInterpIso _ _) (YONEDA ∘F 𝓕 ∘F TautoSem.sem𝓒) (YONEDA ∘F TautoSem.sem𝓓) also-commutes sem𝓒-agree sem𝓓-agree sem𝓕-agree
    where
      also-commutes : NatIso (Id ∘F (YONEDA ∘F (𝓕 ∘F TautoSem.sem𝓒))) ((YONEDA ∘F TautoSem.sem𝓓) ∘F (Freeϕ (Ugr 𝓒) (Ugr 𝓓) (Uhom 𝓕)))
      also-commutes =
        seqNatIso CAT⋆IdR
        (seqNatIso (YONEDA ∘ʳi TautoSem.semF)
                   (CAT⋆Assoc ((Freeϕ (Ugr 𝓒) (Ugr 𝓓) (Uhom 𝓕))) TautoSem.sem𝓓 YONEDA))
      sem𝓒-agree : InterpIso (Ugr 𝓒) 𝓟𝓓
                   ((YONEDA ∘F (𝓕 ∘F TautoSem.sem𝓒)) ∘Interp η (Ugr 𝓒))
                   (Uhom (YONEDA ∘F 𝓕))
      sem𝓒-agree = idInterpIso _ _

      sem𝓓-agree : InterpIso (Ugr 𝓓) 𝓟𝓓
                   ((YONEDA ∘F TautoSem.sem𝓓) ∘Interp ηH (Ugr 𝓒) (Ugr 𝓓) (Uhom 𝓕))
                   (Uhom YONEDA)
      sem𝓓-agree = idInterpIso _ _

      sem𝓕-extends :
        ((also-commutes ⊙ˡInterp η (Ugr 𝓒))
         ⋆InterpIso (YONEDA ∘F TautoSem.sem𝓓 ⊙ʳInterp ηϕ (Ugr 𝓒) (Ugr 𝓓) (Uhom 𝓕)))
                     ≡ idInterpIso (Ugr 𝓒) 𝓟𝓓
      sem𝓕-extends =
        (λ i → simplify i ⋆InterpIso ⊙ʳInterpCompF YONEDA TautoSem.sem𝓓 (ηϕ (Ugr 𝓒) (Ugr 𝓓) (Uhom 𝓕)) i)
        ∙ sym (⊙ʳInterp-CompIso {K = YONEDA} (TautoSem.semF ⊙ˡInterp η (Ugr 𝓒)) (TautoSem.sem𝓓 ⊙ʳInterp ηϕ (Ugr 𝓒) (Ugr 𝓓) (Uhom 𝓕)))
        ∙ cong (_⊙ʳInterp_ YONEDA) TautoSem.semF-extends-ıϕ
        ∙ ⊙ʳInterp-IdIso where
        simplify : (also-commutes ⊙ˡInterp η (Ugr 𝓒)) ≡ (YONEDA ⊙ʳInterp (TautoSem.semF ⊙ˡInterp η (Ugr 𝓒)))
        simplify = InterpIso≡ λ v → 𝓟𝓓 .⋆IdL _ ∙ 𝓟𝓓 .⋆IdR _

      sem𝓕-agree :
        ((Id ⊙ʳInterp symInterpIso sem𝓒-agree)
         ⋆InterpIso ((also-commutes ⊙ˡInterp η (Ugr 𝓒))
         ⋆InterpIso (((YONEDA ∘F TautoSem.sem𝓓) ⊙ʳInterp ηϕ (Ugr 𝓒) (Ugr 𝓓) (Uhom 𝓕))
         ⋆InterpIso (sem𝓓-agree ∘ˡInterp Uhom 𝓕))))
          ≡ idInterpIso (Ugr 𝓒) 𝓟𝓓
      sem𝓕-agree = (λ i → lem1 i ⋆InterpIso (((also-commutes ⊙ˡInterp η (Ugr 𝓒))
         ⋆InterpIso (((YONEDA ∘F TautoSem.sem𝓓) ⊙ʳInterp ηϕ (Ugr 𝓒) (Ugr 𝓓) (Uhom 𝓕))
         ⋆InterpIso (sem𝓓-agree ∘ˡInterp Uhom 𝓕)))))
         ∙ seqInterpIsoIdL _
         ∙ (λ i → (also-commutes ⊙ˡInterp η (Ugr 𝓒)) ⋆InterpIso seqInterpIsoIdR ((YONEDA ∘F TautoSem.sem𝓓) ⊙ʳInterp ηϕ (Ugr 𝓒) (Ugr 𝓓) (Uhom 𝓕)) i)
         ∙ sem𝓕-extends
         where
        lem1 : (Id ⊙ʳInterp symInterpIso sem𝓒-agree) ≡ idInterpIso _ _
        lem1 = InterpIso≡ λ v → refl
  solve : ∀ {A B}
        → (e e' : Free𝓓 [ A , B ])
        → (p : eval e ≡ eval e')
        → TautoSem.sem𝓓 ⟪ e ⟫ ≡ TautoSem.sem𝓓 ⟪ e' ⟫
  solve {A}{B} e e' p = isFaithfulYoneda _ _ _ _ YoTautoe≡YoTautoe' where
    Yoe≡Yoe' : YoSem.sem𝓓 ⟪ e ⟫ ≡ YoSem.sem𝓓 ⟪ e' ⟫
    Yoe≡Yoe' = isoFunInjective (yonedaᴾ _ _) _ _ p

    YoTautoe≡YoTautoe' : YONEDA {C = 𝓓} ⟪ TautoSem.sem𝓓 ⟪ e ⟫ ⟫ ≡ YONEDA ⟪ TautoSem.sem𝓓 ⟪ e' ⟫ ⟫
    YoTautoe≡YoTautoe' = sqRL YoTauto-Yo-Agree
      ∙ (λ i → YoTauto-Yo-Agree .trans .N-ob _ ⋆⟨ 𝓟𝓓 ⟩ Yoe≡Yoe' i ⋆⟨ 𝓟𝓓 ⟩ YoTauto-Yo-Agree .nIso _ .isIso.inv)
      ∙ sym (sqRL YoTauto-Yo-Agree)

solve : (𝓒 : Category ℓc ℓc') (𝓓 : Category ℓd ℓd') (𝓕 : Functor 𝓒 𝓓)
      → {A B : 𝓓 .ob}
      → (e₁ e₂ : Eval.Free𝓓 𝓒 𝓓 𝓕 [ A , B ])
      → (p : Eval.eval 𝓒 𝓓 𝓕 e₁ ≡ Eval.eval 𝓒 𝓓 𝓕 e₂)
      → _
solve = Eval.solve

-- An example (to be moved)
-- F (f ∘ id ∘ g) ∘ h ≡  (F f ∘ id) ∘ (F g ∘ h)
--
example : (𝓒 : Category ℓc ℓc') (𝓓 : Category ℓd ℓd') (𝓕 : Functor 𝓒 𝓓)
        → {A B C : 𝓒 .ob}
        → {D : 𝓓 .ob}
        → (f : 𝓒 [ A , B ])
        → (g : 𝓒 [ B , C ])
        → (h : 𝓓 [ 𝓕 ⟅ C ⟆  , D ])
        → _
example 𝓒 𝓓 𝓕 f g h = solve 𝓒 𝓓 𝓕
  (F⟪ ((↑ f) ⋆ₑ (idₑ ⋆ₑ (↑ g))) ⟫ ⋆f (↑f h))
  (F⟪ idₑ ⋆ₑ (↑ f) ⟫ ⋆f (F⟪ (↑ g) ⋆ₑ idₑ ⟫ ⋆f (↑f h)))
  refl
