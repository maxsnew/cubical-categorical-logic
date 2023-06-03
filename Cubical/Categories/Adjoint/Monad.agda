{-# OPTIONS --safe #-}

module Cubical.Categories.Adjoint.Monad where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Monad.Base
open import Cubical.Categories.Adjoint
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.NaturalTransformation.Properties

open import Cubical.Categories.NaturalTransformation.More

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} (L : Functor C D) (R : Functor D C) where
  open UnitCounit
  open IsMonad
  open _⊣_
  open NatIso

  MonadFromAdjunction : (L ⊣ R) → IsMonad (R ∘F L)
  η (MonadFromAdjunction L⊣R) =  L⊣R .η
  μ (MonadFromAdjunction L⊣R) =
    seqTrans
    -- (RL)(RL) => R(L(RL))
    ((symNatIso (CAT⋆Assoc (R ∘F L) L R)) .trans)
    -- peel off R
    (R ∘ʳ
      -- L(RL) => L
      (seqTrans
        -- L(RL) => (LR)L
        (CAT⋆Assoc L R L .trans)
        -- (LR)L => L
        (seqTrans
          -- (LR)L => 1L
          ((L⊣R .ε) ∘ˡ L)
          -- 1L => L
          (CAT⋆IdR .trans)
        )
      )
    )
  idl-μ (MonadFromAdjunction L⊣R) = {!!}
  idr-μ (MonadFromAdjunction L⊣R) = {!!}
  assoc-μ (MonadFromAdjunction L⊣R) = {!!}
