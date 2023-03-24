{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.Functors.More where

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.NaturalTransformation.Properties
open import Cubical.Categories.Morphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Constructions.BinProduct

private
  variable
    ℓC ℓC' ℓD ℓD' ℓΓ ℓΓ' ℓ ℓ' : Level

module _ (C : Category ℓC ℓC') (D : Category ℓD ℓD') where
  open Category
  open Functor
  open NatTrans

  -- TODO: don't really know what's going on w universes here. Introduced levels ℓ ℓ' not tied to C, D, or Γ in hopes to make this general
  -- The type of this record makes no sense to me at the moment, but does make everything type check.
  -- TODO: Maybe put this is a different file
  record EquivalenceOfCategories {A B : Category ℓ ℓ'}(F : Functor A B) (G : Functor B A) : Type (ℓ-max ℓ ℓ') where
    constructor is-equiv-of-cats
    field
      F∘G-iso-to-id : NatIso (funcComp F G) (Id)
      G∘F-iso-to-id : NatIso (funcComp G F) (Id)

  -- Emily Riehl - Category Theory in Context (CTIC) Lemma 1.5.10
  -- f-induces-unique-map-between-isos : {C : Category ℓ ℓ'} → {a b a' b' : C .ob} →
  -- (f : Hom[ a , b ]) → (ϕ : CatIso a a') → (ψ : CatIso b b') →
  -- Σ[ f' : Hom[ a', b' ] ] (∀ g → (TODO : would need to describe all 4 commuting diags from CTIC here))
  -- TODO: Should just return ψ ∘ f ∘ ϕ

  -- TODO: find proper syntax for existential quantification
  -- Want to show that we have an equivalence of categories iff ess surj on objs, full, faithful
  -- Want to just follow CTIC Theorem 1.5.9, but that uses choice
  alt-equiv-of-categories-forward : {A B : Category ℓ ℓ'} → (F : Functor A B) →
    isFull F →
    isFaithful F →
    isEssentiallySurj F →
    Σ[ G ∈ Functor B A ] EquivalenceOfCategories F G
  alt-equiv-of-categories-forward _ = {!!}

  appF : Functor ((FUNCTOR C D) ×C C) D
  appF .F-ob (F , c) = F ⟅ c ⟆
  appF .F-hom {x = (F , c)}{y = (F' , c')} (α , f) = F ⟪ f ⟫ ⋆⟨ D ⟩ α .N-ob c'
  appF .F-id {x = (F , c)}=
    F ⟪ C .id ⟫ ⋆⟨ D ⟩ D .id ≡[ i ]⟨ F .F-id i ⋆⟨ D ⟩ D .id ⟩
    D .id ⋆⟨ D ⟩ D .id ≡⟨ D .⋆IdR (D .id) ⟩
    D .id ∎
  appF .F-seq {x = (F , c)}{y = (F' , c')}{z = (F'' , c'')}(α , f) (α' , f') =
    -- Functor solver would be useful here...
    F ⟪ f ⋆⟨ C ⟩ f' ⟫ ⋆⟨ D ⟩ (α .N-ob _ ⋆⟨ D ⟩ α' .N-ob c'')
      ≡[ i ]⟨ F .F-seq f f' i ⋆⟨ D ⟩ (α .N-ob _ ⋆⟨ D ⟩ α' .N-ob c'') ⟩
    (F ⟪ f ⟫ ⋆⟨ D ⟩ F ⟪ f' ⟫) ⋆⟨ D ⟩ (α .N-ob _ ⋆⟨ D ⟩ α' .N-ob c'')
      ≡⟨ D .⋆Assoc (F ⟪ f ⟫) (F ⟪ f' ⟫) ((α .N-ob _ ⋆⟨ D ⟩ α' .N-ob c'')) ⟩
    F ⟪ f ⟫ ⋆⟨ D ⟩ (F ⟪ f' ⟫ ⋆⟨ D ⟩ (α .N-ob _ ⋆⟨ D ⟩ α' .N-ob c''))
      ≡[ i ]⟨ F ⟪ f ⟫ ⋆⟨ D ⟩ D .⋆Assoc (F ⟪ f' ⟫) (α .N-ob _) (α' .N-ob c'') (~ i) ⟩
    F ⟪ f ⟫ ⋆⟨ D ⟩ ((F ⟪ f' ⟫ ⋆⟨ D ⟩ α .N-ob _) ⋆⟨ D ⟩ α' .N-ob c'')
      ≡[ i ]⟨ F ⟪ f ⟫ ⋆⟨ D ⟩ (α .N-hom f' i ⋆⟨ D ⟩ α' .N-ob c'') ⟩
    F ⟪ f ⟫ ⋆⟨ D ⟩ ((α .N-ob _ ⋆⟨ D ⟩ F' ⟪ f' ⟫) ⋆⟨ D ⟩ α' .N-ob c'')
      ≡[ i ]⟨ F ⟪ f ⟫ ⋆⟨ D ⟩ D .⋆Assoc (α .N-ob _) (F' ⟪ f' ⟫) (α' .N-ob c'') i ⟩
    F ⟪ f ⟫ ⋆⟨ D ⟩ (α .N-ob _ ⋆⟨ D ⟩ (F' ⟪ f' ⟫ ⋆⟨ D ⟩ α' .N-ob c''))
      ≡[ i ]⟨ D .⋆Assoc (F ⟪ f ⟫) (α .N-ob _) ((F' ⟪ f' ⟫ ⋆⟨ D ⟩ α' .N-ob c'')) (~ i) ⟩
    (F ⟪ f ⟫ ⋆⟨ D ⟩ α .N-ob c') ⋆⟨ D ⟩ (F' ⟪ f' ⟫ ⋆⟨ D ⟩ α' .N-ob c'') ∎

  module _ {Γ : Category ℓΓ ℓΓ'} where
    λF : Functor (Γ ×C C) D → Functor Γ (FUNCTOR C D)
    λF F .F-ob a .F-ob b = F ⟅ a , b ⟆
    λF F .F-ob a .F-hom f = F .F-hom (Γ .id , f)
    λF F .F-ob a .F-id = F .F-id
    λF F .F-ob a .F-seq f g =
      F .F-hom (Γ .id , f ⋆⟨ C ⟩ g)
        ≡[ i ]⟨ F .F-hom ((Γ .⋆IdL (Γ .id) (~ i)) , f ⋆⟨ C ⟩ g) ⟩
      F .F-hom (Γ .id ⋆⟨ Γ ⟩ Γ .id , f ⋆⟨ C ⟩ g)
        ≡⟨ F .F-seq (Γ .id , f) (Γ .id , g) ⟩
      F .F-hom (Γ .id , f) ⋆⟨ D ⟩ F .F-hom (Γ .id , g ) ∎
    λF F .F-hom γ .N-ob b = F .F-hom (γ , C .id)
    λF F .F-hom γ .N-hom f =
      F .F-hom (Γ .id , f) ⋆⟨ D ⟩ F .F-hom (γ , C .id)
        ≡⟨ sym (F .F-seq (Γ .id , f) (γ , C .id)) ⟩
      F .F-hom (Γ .id ⋆⟨ Γ ⟩ γ , f ⋆⟨ C ⟩ C .id)
        ≡[ i ]⟨ F .F-hom ((idTrans (Id {C = Γ}) .N-hom γ (~ i)) , idTrans (Id {C = C}) .N-hom f i) ⟩
      F .F-hom (γ ⋆⟨ Γ ⟩ Γ .id , C .id ⋆⟨ C ⟩ f)
        ≡⟨ F .F-seq (γ , C .id) (Γ .id , f) ⟩
      F .F-hom (γ , C .id) ⋆⟨ D ⟩ F .F-hom (Γ .id , f)  ∎
    λF F .F-id = makeNatTransPath (funExt (λ a → F .F-id))
    λF F .F-seq γ δ = makeNatTransPath (funExt (λ a →
        F .F-hom (γ ⋆⟨ Γ ⟩ δ , C .id)
          ≡[ i ]⟨ F .F-hom (γ ⋆⟨ Γ ⟩ δ , C .⋆IdL (C .id) (~ i)) ⟩
        F .F-hom (γ ⋆⟨ Γ ⟩ δ , C .id ⋆⟨ C ⟩ C .id)
          ≡⟨ F .F-seq (γ , C .id) (δ , C .id) ⟩
        F .F-hom (γ , C .id) ⋆⟨ D ⟩ F .F-hom (δ , C .id) ∎))

    λFl : Functor (C ×C Γ) D → Functor Γ (FUNCTOR C D)
    λFl F = λF (F ∘F (Snd Γ C ,F Fst Γ C))
