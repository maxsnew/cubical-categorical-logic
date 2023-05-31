{-# OPTIONS --safe #-}
module Cubical.Categories.Comonad.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor renaming (𝟙⟨_⟩ to funcId)
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.NaturalTransformation.Properties
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Constructions.BinProduct

private
  variable
    ℓ ℓ' : Level

module _ {C : Category ℓ ℓ'} (W : Functor C C) where
  open Category C
  open Functor
  open NatTrans

  record IsComonad : Type (ℓ-max ℓ ℓ') where
    field
      ε : NatTrans W (funcId C)
      δ : NatTrans W (funcComp W W)
      idl-δ : PathP (λ i → NatTrans W (F-rUnit {F = W} i)) ((ε ∘ˡ W) ∘ᵛ δ) (idTrans W)
      idr-δ : PathP (λ i → NatTrans W (F-lUnit {F = W} i)) ((W ∘ʳ ε) ∘ᵛ δ) (idTrans W)
      -- This is the obvious definition, but F-assoc is bad definitionally
      -- assoc-δ : PathP (λ i → NatTrans W (F-assoc {F = W} {G = W} {H = W} i))
      --                 ((W ∘ʳ δ) ∘ᵛ δ)
      --                 ((δ ∘ˡ W) ∘ᵛ δ)
      assoc-δ : ∀ {c} → ((W ∘ʳ δ) ∘ᵛ δ) ⟦ c ⟧ ≡ ((δ ∘ˡ W) ∘ᵛ δ) ⟦ c ⟧
    -- TODO: make this a NatTrans
    extend : ∀ {c d} → C [ W ⟅ c ⟆ , d ] → C [ W ⟅ c ⟆ , W ⟅ d ⟆ ]
    extend f = W ⟪ f ⟫ ∘⟨ C ⟩ δ .N-ob _

    extend-ε : ∀ {c} → extend (ε ⟦ c ⟧) ≡ id
    extend-ε = λ i → idr-δ i ⟦ _ ⟧
module _ (C : Category ℓ ℓ') where
  Comonad : Type (ℓ-max ℓ ℓ')
  Comonad = Σ[ D ∈ Functor C C ] IsComonad D

module _ {C : Category ℓ ℓ'} (coW coV : Comonad C) (ν : NatTrans (fst coW) (fst coV)) where

  private
    W V : Functor C C
    W = fst coW
    V = fst coV
    module W = IsComonad (snd coW)
    module V = IsComonad (snd coV)

  record IsComonadHom : Type (ℓ-max ℓ ℓ') where
    constructor proveComonadHom
    field
      V-ε : V.ε ∘ᵛ ν ≡ W.ε
      V-δ : V.δ ∘ᵛ ν ≡ (ν ∘ʰ ν) ∘ᵛ W.δ
  open IsComonadHom

  isProp-IsComnadHom : isProp (IsComonadHom)
  isProp-IsComnadHom ν ν' i .V-ε = isSetNatTrans _ _ (ν .V-ε) (ν' .V-ε) i
  isProp-IsComnadHom ν ν' i .V-δ = isSetNatTrans _ _ (ν .V-δ) (ν' .V-δ) i

module _ {C : Category ℓ ℓ'} (comonadW comonadV : Comonad C) where
  ComonadHom : Type (ℓ-max ℓ ℓ')
  ComonadHom = Σ[ ν ∈ NatTrans (fst comonadW) (fst comonadV) ] IsComonadHom comonadW comonadV ν
