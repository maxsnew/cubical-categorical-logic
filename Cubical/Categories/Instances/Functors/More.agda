{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.Functors.More where

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.NaturalTransformation.Properties
open import Cubical.Categories.Morphism
open import Cubical.Foundations.Prelude hiding (≡⟨⟩-syntax; _≡⟨_⟩_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Cubical.Categories.Functor.Properties
open import Cubical.Categories.Equivalence.Base
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Categories.Category

open import AltEquationalReasoning
open import Cubical.Tactics.CategorySolver.Reflection

private
  variable
    ℓC ℓC' ℓD ℓD' ℓΓ ℓΓ' ℓ ℓ' : Level

module _ (C : Category ℓC ℓC') (D : Category ℓD ℓD') where
  open Category
  open Functor
  open NatTrans

  appF : Functor ((FUNCTOR C D) ×C C) D
  appF .F-ob (F , c) = F ⟅ c ⟆
  appF .F-hom {x = (F , c)}{y = (F' , c')} (α , f) = F ⟪ f ⟫ ⋆⟨ D ⟩ α .N-ob c'
  appF .F-id {x = (F , c)}=
    (F ⟪ C .id ⟫ ⋆⟨ D ⟩ D .id) ≡⟨ (λ i → F .F-id i ⋆⟨ D ⟩ D .id) ⟩
    (D .id ⋆⟨ D ⟩ D .id) ≡⟨ D .⋆IdR (D .id) ⟩
    (D .id) ∎
  appF .F-seq {x = (F , c)}{y = (F' , c')}{z = (F'' , c'')}(α , f) (α' , f') =
    F ⟪ f ⋆⟨ C ⟩ f' ⟫ ⋆⟨ D ⟩ (α .N-ob _ ⋆⟨ D ⟩ α' .N-ob c'')
      ≡⟨ (λ i → F .F-seq f f' i ⋆⟨ D ⟩ (α .N-ob _ ⋆⟨ D ⟩ α' .N-ob c'')) ⟩
    F ⟪ f ⟫ ⋆⟨ D ⟩ F ⟪ f' ⟫ ⋆⟨ D ⟩ (α .N-ob _ ⋆⟨ D ⟩ α' .N-ob c'')
      ≡⟨ solveCat! D ⟩
    F ⟪ f ⟫ ⋆⟨ D ⟩ ((F ⟪ f' ⟫ ⋆⟨ D ⟩ α .N-ob _) ⋆⟨ D ⟩ α' .N-ob c'')
      ≡⟨ (λ i → F ⟪ f ⟫ ⋆⟨ D ⟩ (α .N-hom f' i ⋆⟨ D ⟩ α' .N-ob c'')) ⟩
    F ⟪ f ⟫ ⋆⟨ D ⟩ ((α .N-ob _ ⋆⟨ D ⟩ F' ⟪ f' ⟫) ⋆⟨ D ⟩ α' .N-ob c'')
      ≡⟨ solveCat! D ⟩
    (F ⟪ f ⟫ ⋆⟨ D ⟩ α .N-ob c') ⋆⟨ D ⟩ (F' ⟪ f' ⟫ ⋆⟨ D ⟩ α' .N-ob c'') ∎

  module _ {Γ : Category ℓΓ ℓΓ'} where
    λFr : Functor (Γ ×C C) D → Functor Γ (FUNCTOR C D)
    λFr F .F-ob a .F-ob b = F ⟅ a , b ⟆
    λFr F .F-ob a .F-hom f = F .F-hom (Γ .id , f)
    λFr F .F-ob a .F-id = F .F-id
    λFr F .F-ob a .F-seq f g =
      F .F-hom (Γ .id , f ⋆⟨ C ⟩ g)
        ≡⟨ (λ i → F .F-hom ((Γ .⋆IdL (Γ .id) (~ i)) , f ⋆⟨ C ⟩ g)) ⟩
      F .F-hom (Γ .id ⋆⟨ Γ ⟩ Γ .id , f ⋆⟨ C ⟩ g)
        ≡⟨ F .F-seq (Γ .id , f) (Γ .id , g) ⟩
      F .F-hom (Γ .id , f) ⋆⟨ D ⟩ F .F-hom (Γ .id , g ) ∎
    λFr F .F-hom γ .N-ob b = F .F-hom (γ , C .id)
    λFr F .F-hom γ .N-hom f =
      F .F-hom (Γ .id , f) ⋆⟨ D ⟩ F .F-hom (γ , C .id)
        ≡⟨ sym (F .F-seq (Γ .id , f) (γ , C .id)) ⟩
      F .F-hom (Γ .id ⋆⟨ Γ ⟩ γ , f ⋆⟨ C ⟩ C .id)
        ≡⟨ (λ i → F .F-hom ((idTrans (Id {C = Γ}) .N-hom γ (~ i)) , idTrans (Id {C = C}) .N-hom f i)) ⟩
      F .F-hom (γ ⋆⟨ Γ ⟩ Γ .id , C .id ⋆⟨ C ⟩ f)
        ≡⟨ F .F-seq (γ , C .id) (Γ .id , f) ⟩
      F .F-hom (γ , C .id) ⋆⟨ D ⟩ F .F-hom (Γ .id , f)  ∎
    λFr F .F-id = makeNatTransPath (funExt (λ a → F .F-id))
    λFr F .F-seq γ δ = makeNatTransPath (funExt (λ a →
        F .F-hom (γ ⋆⟨ Γ ⟩ δ , C .id)
          ≡⟨ (λ i → F .F-hom (γ ⋆⟨ Γ ⟩ δ , C .⋆IdL (C .id) (~ i))) ⟩
        F .F-hom (γ ⋆⟨ Γ ⟩ δ , C .id ⋆⟨ C ⟩ C .id)
          ≡⟨ F .F-seq (γ , C .id) (δ , C .id) ⟩
        F .F-hom (γ , C .id) ⋆⟨ D ⟩ F .F-hom (δ , C .id) ∎))

    -- TODO: come up with a better name for this
    λF-functor : Functor (FUNCTOR (Γ ×C C) D) (FUNCTOR Γ (FUNCTOR C D))
    λF-functor .F-ob = λFr
    λF-functor .F-hom η .N-ob γ .N-ob c = η .N-ob (γ , c)
    λF-functor .F-hom η .N-ob γ .N-hom ϕ = η .N-hom (Γ .id , ϕ)
    λF-functor .F-hom η .N-hom f = makeNatTransPath (funExt (λ (c : C .ob) → η .N-hom (f , C .id)))
    λF-functor .F-id = makeNatTransPath (funExt λ (γ : Γ .ob) → refl)
    λF-functor .F-seq η η' = makeNatTransPath (funExt λ (γ : Γ .ob) → refl)


    -- Preimage for the fullness proof
    preimage : {F G : Functor (Γ ×C C) D} (λη : NatTrans (λF-functor .F-ob F) (λF-functor .F-ob G)) → (NatTrans F G)
    preimage {F} {G} λη .N-ob (γ , c) = λη .N-ob γ .N-ob c
    preimage {F} {G} λη .N-hom {(γ₁ , c₁)} {(γ₂ , c₂)} (ϕ₁ , ϕ₂) =
      F .F-hom (ϕ₁ , ϕ₂) ⋆⟨ D ⟩ preimage λη .N-ob (γ₂ , c₂)
        ≡⟨ (λ i → (F .F-hom ((Γ .⋆IdR ϕ₁) (~ i) , (C .⋆IdL ϕ₂) (~ i)) ⋆⟨ D ⟩ preimage λη .N-ob (γ₂ , c₂))) ⟩
      F .F-hom ((ϕ₁ , C .id) ⋆⟨ Γ ×C C ⟩ (Γ .id , ϕ₂)) ⋆⟨ D ⟩ preimage λη .N-ob (γ₂ , c₂)
        ≡⟨ (λ i → (F .F-seq (ϕ₁ , C .id) (Γ .id , ϕ₂)) (i) ⋆⟨ D ⟩ preimage λη .N-ob (γ₂ , c₂)) ⟩
      F .F-hom (ϕ₁ , C .id) ⋆⟨ D ⟩ F .F-hom (Γ .id , ϕ₂) ⋆⟨ D ⟩ preimage λη .N-ob (γ₂ , c₂)
        ≡⟨ D .⋆Assoc (F .F-hom (ϕ₁ , C .id)) (F .F-hom (Γ .id , ϕ₂) ) (preimage λη .N-ob (γ₂ , c₂)) ⟩
      F .F-hom (ϕ₁ , C .id) ⋆⟨ D ⟩ (F .F-hom (Γ .id , ϕ₂) ⋆⟨ D ⟩ preimage λη .N-ob (γ₂ , c₂))
        ≡⟨ ((λ i → ((F .F-hom (ϕ₁ , C .id)) ⋆⟨ D ⟩ (λη .N-ob γ₂ .N-hom ϕ₂ (i))))) ⟩
      F .F-hom (ϕ₁ , C .id) ⋆⟨ D ⟩ (preimage λη .N-ob (γ₂ , c₁) ⋆⟨ D ⟩ G .F-hom (Γ .id , ϕ₂))
        ≡⟨  sym (D .⋆Assoc (F .F-hom (ϕ₁ , C .id)) (preimage λη .N-ob (γ₂ , c₁)) (G .F-hom (Γ .id , ϕ₂)))  ⟩
      (F .F-hom (ϕ₁ , C .id) ⋆⟨ D ⟩ preimage λη .N-ob (γ₂ , c₁)) ⋆⟨ D ⟩ G .F-hom (Γ .id , ϕ₂)
        ≡⟨ ((λ i → ( ((λη .N-hom ϕ₁ (i)) .N-ob c₁) ⋆⟨ D ⟩ G .F-hom (Γ .id , ϕ₂) ))) ⟩
      (preimage λη .N-ob (γ₁ , c₁) ⋆⟨ D ⟩ G .F-hom (ϕ₁ , C .id)) ⋆⟨ D ⟩ G .F-hom (Γ .id , ϕ₂)
        ≡⟨ D .⋆Assoc (preimage λη .N-ob (γ₁ , c₁)) (G .F-hom (ϕ₁ , C .id)) (G .F-hom (Γ .id , ϕ₂)) ⟩
      preimage λη .N-ob (γ₁ , c₁) ⋆⟨ D ⟩ (G .F-hom (ϕ₁ , C .id) ⋆⟨ D ⟩ G .F-hom (Γ .id , ϕ₂))
        ≡⟨ ((λ i → (preimage λη .N-ob (γ₁ , c₁) ⋆⟨ D ⟩ (G .F-seq (ϕ₁ , C .id) (Γ .id , ϕ₂)) (~ i) ))) ⟩
      preimage λη .N-ob (γ₁ , c₁) ⋆⟨ D ⟩ (G .F-hom ((ϕ₁ , C .id) ⋆⟨ Γ ×C C ⟩ (Γ .id , ϕ₂)))
        ≡⟨ ((λ i → (preimage λη .N-ob (γ₁ , c₁) ⋆⟨ D ⟩ (G .F-hom (((Γ .⋆IdR ϕ₁) i), ((C .⋆IdL ϕ₂) i))) ))) ⟩
      preimage λη .N-ob (γ₁ , c₁) ⋆⟨ D ⟩ G .F-hom (ϕ₁ , ϕ₂) ∎

    λF-isFull : isFull λF-functor
    λF-isFull F G λη =  (∣ preimage λη , makeNatTransPath (funExt (λ (γ : Γ .ob) →
      makeNatTransPath (funExt (λ (c : C .ob) →
        λF-functor .F-hom (preimage λη) .N-ob γ .N-ob c
        ≡⟨ refl ⟩
        λη .N-ob γ .N-ob c ∎))
      ) ) ∣₁)

    -- TODO : λF is especially badly named in the context of all these other names
    preimage-obj : (FUNCTOR Γ (FUNCTOR C D)) .ob → (FUNCTOR (Γ ×C C) D) .ob
    preimage-obj λF .F-ob (γ , c) =  λF .F-ob γ .F-ob c
    preimage-obj λF .F-hom {x = (γ₁ , c₁)} {y = (γ₂ , c₂)} (ϕ , ψ) = λF .F-hom ϕ .N-ob c₁ ⋆⟨ D ⟩ λF .F-ob γ₂ .F-hom ψ
    preimage-obj λF .F-seq {x = (γ₁ , c₁)} {y = (γ₂ , c₂)} {z = (γ₃ , c₃)} (ϕ₁ , ψ₁) (ϕ₂ , ψ₂) = (
      preimage-obj λF .F-hom ((ϕ₁ , ψ₁) ⋆⟨ Γ ×C C ⟩ (ϕ₂ , ψ₂))
        ≡⟨ ((λ i → ( (λF .F-seq ϕ₁ ϕ₂ (i) ) .N-ob c₁ ⋆⟨ D ⟩ λF .F-ob γ₃ .F-hom (ψ₁ ⋆⟨ C ⟩ ψ₂)))) ⟩
      (λF .F-hom ϕ₁ ⋆⟨ FUNCTOR C D ⟩ λF .F-hom ϕ₂) .N-ob c₁ ⋆⟨ D ⟩ λF .F-ob γ₃ .F-hom (ψ₁ ⋆⟨ C ⟩ ψ₂)
        ≡⟨ (λ i → (λF .F-hom ϕ₁ .N-ob c₁ ⋆⟨ D ⟩ λF .F-hom ϕ₂ .N-ob c₁ ⋆⟨ D ⟩ λF .F-ob γ₃ .F-seq ψ₁ ψ₂ i)) ⟩
      (λF .F-hom ϕ₁ .N-ob c₁ ⋆⟨ D ⟩ λF .F-hom ϕ₂ .N-ob c₁) ⋆⟨ D ⟩ (λF .F-ob γ₃ .F-hom ψ₁ ⋆⟨ D ⟩ λF .F-ob γ₃ .F-hom ψ₂)
        ≡⟨ solveCat! D ⟩
      λF .F-hom ϕ₁ .N-ob c₁ ⋆⟨ D ⟩ (λF .F-hom ϕ₂ .N-ob c₁ ⋆⟨ D ⟩ λF .F-ob γ₃ .F-hom ψ₁) ⋆⟨ D ⟩ λF .F-ob γ₃ .F-hom ψ₂
        ≡⟨ ((λ i → ( λF .F-hom ϕ₁ .N-ob c₁ ⋆⟨ D ⟩ (λF .F-hom ϕ₂ .N-hom ψ₁ (~ i) ) ⋆⟨ D ⟩ λF .F-ob γ₃ .F-hom ψ₂ ))) ⟩
      λF .F-hom ϕ₁ .N-ob c₁ ⋆⟨ D ⟩ (λF .F-ob γ₂ .F-hom ψ₁ ⋆⟨ D ⟩ λF .F-hom ϕ₂ .N-ob c₂) ⋆⟨ D ⟩ λF .F-ob γ₃ .F-hom ψ₂
        ≡⟨ solveCat! D ⟩
      preimage-obj λF .F-hom (ϕ₁ , ψ₁) ⋆⟨ D ⟩ preimage-obj λF .F-hom (ϕ₂ , ψ₂) ∎)
    preimage-obj λF .F-id  {x = (γ , c)} = (
      preimage-obj λF .F-hom (Γ .id , C .id)
        ≡⟨ ((λ i → (λF .F-id i .N-ob c ⋆⟨ D ⟩ λF .F-ob γ .F-hom (C .id)))) ⟩
      D .id ⋆⟨ D ⟩ λF .F-ob γ .F-hom (C .id)
        ≡⟨ ((λ i → (D .id ⋆⟨ D ⟩ (λF .F-ob γ .F-id i)))) ⟩
      D .id ⋆⟨ D ⟩ D .id
        ≡⟨ D .⋆IdL (D .id) ⟩
      D .id
      ∎ )
    preimage-iso : (λF : (FUNCTOR Γ (FUNCTOR C D)) .ob) → NatTrans (λF-functor .F-ob (preimage-obj λF)) λF
    preimage-iso λF .N-ob γ .N-ob c = D .id
    preimage-iso λF .N-ob γ .N-hom {x = c₁} {y = c₂} ψ =
      ((λF .F-hom (Γ .id) .N-ob c₁) ⋆⟨ D ⟩ (λF .F-ob γ .F-hom ψ)) ⋆⟨ D ⟩ D .id
        ≡⟨ (λ i → (D .⋆IdR ((λF .F-hom (Γ .id) .N-ob c₁) ⋆⟨ D ⟩ (λF .F-ob γ .F-hom ψ)) (i) )) ⟩
      (λF .F-hom (Γ .id) .N-ob c₁) ⋆⟨ D ⟩ λF .F-ob γ .F-hom ψ
        ≡⟨ ((λ i → ((λF .F-id i) .N-ob c₁ ⋆⟨ D ⟩ λF .F-ob γ .F-hom ψ ))) ⟩
      D .id ⋆⟨ D ⟩ λF .F-ob γ .F-hom ψ ∎
    preimage-iso λF .N-hom {x = γ₁} {y = γ₂} ϕ = makeNatTransPath (funExt (λ (c : C .ob) →
      λF-functor .F-ob (preimage-obj λF) .F-hom ϕ .N-ob c ⋆⟨ D ⟩ (preimage-iso λF) .N-ob γ₂ .N-ob c
        ≡⟨ D .⋆IdR (λF-functor .F-ob (preimage-obj λF) .F-hom ϕ .N-ob c) ⟩
      λF .F-hom ϕ .N-ob c ⋆⟨ D ⟩ λF .F-ob γ₂ .F-hom (C .id)
        ≡⟨ ((λ i → (λF .F-hom ϕ .N-ob c ⋆⟨ D ⟩ λF .F-ob γ₂ .F-id i))) ⟩
      λF .F-hom ϕ .N-ob c ⋆⟨ D ⟩ D .id
        ≡⟨ D .⋆IdR (λF .F-hom ϕ .N-ob c) ⟩
      λF .F-hom ϕ .N-ob c
        ≡⟨ ((λ i → (D .⋆IdL (λF .F-hom ϕ .N-ob c) (~ i) ))) ⟩
      (preimage-iso λF) .N-ob γ₁ .N-ob c ⋆⟨ D ⟩ λF .F-hom ϕ .N-ob c ∎))

    open isIso

    preimage-iso-isIso : (λF : (FUNCTOR Γ (FUNCTOR C D)) .ob) → isIsoC (FUNCTOR Γ (FUNCTOR C D)) (preimage-iso λF)
    preimage-iso-isIso λF .inv .N-ob γ .N-ob c =  D .id
    preimage-iso-isIso λF .inv .N-ob γ .N-hom {x = c₁} {y = c₂} ψ =
      λF .F-ob γ .F-hom ψ ⋆⟨ D ⟩ D .id
        ≡⟨ D .⋆IdR (λF .F-ob γ .F-hom ψ) ⟩
      λF .F-ob γ .F-hom ψ
        ≡⟨ (λ i → (D .⋆IdL (λF .F-ob γ .F-hom ψ) (~ i))) ⟩
      D .id ⋆⟨ D ⟩ λF .F-ob γ .F-hom ψ
        ≡⟨ ((λ i → (λF .F-id (~ i)) .N-ob c₁ ⋆⟨ D ⟩ λF .F-ob γ .F-hom ψ ) ) ⟩
     λF-functor .F-ob (preimage-obj λF) .F-ob γ .F-hom ψ
        ≡⟨ ((λ i → (D .⋆IdL (λF-functor .F-ob (preimage-obj λF) .F-ob γ .F-hom ψ ) (~ i) ))) ⟩
      D .id ⋆⟨ D ⟩ λF-functor .F-ob (preimage-obj λF) .F-ob γ .F-hom ψ ∎
    preimage-iso-isIso λF .inv .N-hom {x = γ₁} {y = γ₂} ϕ = makeNatTransPath (funExt (λ (c : C .ob ) →
      λF .F-hom ϕ .N-ob c ⋆⟨ D ⟩ preimage-iso-isIso λF .inv .N-ob γ₂ .N-ob c
        ≡⟨ D .⋆IdR (λF .F-hom ϕ .N-ob c) ⟩
      λF .F-hom ϕ .N-ob c
        ≡⟨ ((λ i → (D .⋆IdR (λF .F-hom ϕ .N-ob c) (~ i)))) ⟩
      λF .F-hom ϕ .N-ob c ⋆⟨ D ⟩ D .id
        ≡⟨ ((λ i → ( λF .F-hom ϕ .N-ob c ⋆⟨ D ⟩ λF .F-ob γ₂ .F-id (~ i )))) ⟩
      λFr (preimage-obj λF) .F-hom ϕ .N-ob c
        ≡⟨ ((λ i → ((D .⋆IdL (λFr (preimage-obj λF) .F-hom ϕ .N-ob c) (~ i)) ))) ⟩
      D .id ⋆⟨ D ⟩ λFr (preimage-obj λF) .F-hom ϕ .N-ob c ∎
      ))
    preimage-iso-isIso λF .sec = makeNatTransPath (funExt (λ (γ : Γ .ob) →
      makeNatTransPath (funExt (λ (c : C .ob) →
        preimage-iso-isIso λF .inv .N-ob γ .N-ob c ⋆⟨ D ⟩ preimage-iso λF .N-ob γ .N-ob c
          ≡⟨ D .⋆IdR (preimage-iso-isIso λF .inv .N-ob γ .N-ob c) ⟩
        D .id ∎
      ))))
    preimage-iso-isIso λF .ret = makeNatTransPath (funExt (λ (γ : Γ .ob) →
      makeNatTransPath (funExt (λ (c : C .ob) →
         preimage-iso λF .N-ob γ .N-ob c ⋆⟨ D ⟩ preimage-iso-isIso λF .inv .N-ob γ .N-ob c
          ≡⟨ D .⋆IdR (preimage-iso-isIso λF .inv .N-ob γ .N-ob c) ⟩
        D .id ∎
      ))))


    λF-ess-surj : isEssentiallySurj λF-functor
    λF-ess-surj λF = ( ∣ preimage-obj λF , (preimage-iso λF , preimage-iso-isIso λF) ∣₁ )

    λF-isFaithful : isFaithful λF-functor
    λF-isFaithful F G η₁ η₂ λη₁≡λη₂ = makeNatTransPath (funExt (λ (γ , c) →
      η₁ .N-ob (γ , c)
      ≡⟨ (λ i → λη₁≡λη₂ i .N-ob γ .N-ob c) ⟩
       η₂ .N-ob (γ , c) ∎))

    λF-isFullyFaithful : isFullyFaithful λF-functor
    λF-isFullyFaithful = isFull+Faithful→isFullyFaithful {F = λF-functor} λF-isFull λF-isFaithful

    open isWeakEquivalence

    λF-isWeakEquiv : isWeakEquivalence λF-functor
    λF-isWeakEquiv .fullfaith = λF-isFullyFaithful
    λF-isWeakEquiv .esssurj = λF-ess-surj

    -- open isUnivalent

    -- λF-isEquivalence : isEquivalence λF-functor
    -- λF-isEquivalence = isWeakEquiv→isEquiv λF-isWeakEquiv

    -- open _≃ᶜ_

    -- curryEquivalence : FUNCTOR (Γ ×C C) D ≃ᶜ FUNCTOR Γ (FUNCTOR C D)
    -- curryEquivalence .func = λF-functor
    -- curryEquivalence .isEquiv = λF-isEquivalence where
    --   open Cubical.Categories.Equivalence.Base.

    λFl : Functor (C ×C Γ) D → Functor Γ (FUNCTOR C D)
    λFl F = λFr (F ∘F (Snd Γ C ,F Fst Γ C))
