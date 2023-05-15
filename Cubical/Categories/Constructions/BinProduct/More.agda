-- Product of two categories
{-# OPTIONS --safe #-}

module Cubical.Categories.Constructions.BinProduct.More where

open import Cubical.Categories.Constructions.BinProduct

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functors.Constant

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level



-- helpful decomposition of morphisms used in several proofs
-- about product category

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}{E : Category ℓE ℓE'} where

  open Category
  open Functor

  BinMorphDecompL : ∀ {x1 x2} {y1 y2} ((f , g) : (C ×C D) [ (x1 , y1) , (x2 , y2) ])
                      → (F : Functor (C ×C D) E) 
                      → (F ⟪ f , g ⟫) ≡ (F ⟪ f , D .id ⟫) ⋆⟨ E ⟩ (F ⟪ C .id , g ⟫)
  BinMorphDecompL (f , g) F =
    (F ⟪ f , g ⟫)
      ≡⟨ (λ i → F ⟪ C .⋆IdR f (~ i), D .⋆IdL g (~ i)⟫) ⟩
    (F ⟪ f ⋆⟨ C ⟩ C .id , D .id ⋆⟨ D ⟩ g ⟫)
      ≡⟨ F .F-seq (f , D .id) (C .id , g) ⟩
    (F ⟪ f , D .id ⟫) ⋆⟨ E ⟩ (F ⟪ C .id , g ⟫) ∎

  BinMorphDecompR : ∀ {x1 x2} {y1 y2} ((f , g) : (C ×C D) [ (x1 , y1) , (x2 , y2) ])
                      → (F : Functor (C ×C D) E) 
                      → (F ⟪ f , g ⟫) ≡ (F ⟪ C .id , g ⟫) ⋆⟨ E ⟩ (F ⟪ f , D .id ⟫)
  BinMorphDecompR (f , g) F =
    (F ⟪ f , g ⟫)
      ≡⟨ (λ i → F ⟪ C .⋆IdL f (~ i), D .⋆IdR g (~ i)⟫) ⟩
    (F ⟪ C .id ⋆⟨ C ⟩ f , g ⋆⟨ D ⟩ D .id ⟫)
      ≡⟨ F .F-seq (C .id , g) (f , D .id) ⟩
    (F ⟪ C .id , g ⟫) ⋆⟨ E ⟩ (F ⟪ f , D .id ⟫) ∎