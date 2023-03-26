-- Free category over a directed graph/quiver
{-# OPTIONS --safe #-}

module Cubical.Categories.Constructions.Free.General where

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Data.Graph.Base
open import Cubical.Data.Graph.Path
open import Cubical.Foundations.Prelude hiding (Path)

module _ {ℓv ℓe : Level} where
  module _ (G : Graph ℓv ℓe) where
    data Exp : G .Node → G .Node → Type (ℓ-max ℓv ℓe) where
      ↑_   : ∀ {A B} → G .Edge A B → Exp A B
      idₑ  : ∀ {Γ} → Exp Γ Γ
      _⋆ₑ_ : ∀ {A B C} → Exp A B → Exp B C → Exp A C
      ⋆ₑIdL : ∀ {A B} (e : Exp A B) → idₑ ⋆ₑ e ≡ e
      ⋆ₑIdR : ∀ {A B} (e : Exp A B) → e ⋆ₑ idₑ ≡ e
      ⋆ₑAssoc : ∀ {A B C D} (e : Exp A B)(f : Exp B C)(g : Exp C D)
              → (e ⋆ₑ f) ⋆ₑ g ≡ e ⋆ₑ (f ⋆ₑ g)
      isSetExp : ∀ {A B} → isSet (Exp A B)

    open Category
    FreeCat : Category ℓv (ℓ-max ℓv ℓe)
    FreeCat .ob = G .Node
    FreeCat .Hom[_,_] = Exp
    FreeCat .id = idₑ
    FreeCat ._⋆_ = _⋆ₑ_
    FreeCat .⋆IdL = ⋆ₑIdL
    FreeCat .⋆IdR = ⋆ₑIdR
    FreeCat .⋆Assoc = ⋆ₑAssoc
    FreeCat .isSetHom = isSetExp

    -- Underlying graph of a category
    Ugr : ∀ {ℓc ℓc'} (𝓒 : Category ℓc ℓc') → Graph ℓc ℓc'
    Ugr 𝓒 .Node = 𝓒 .ob
    Ugr 𝓒 .Edge = 𝓒 .Hom[_,_]

    η : GraphHom G (Ugr FreeCat)
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
      ⟦ isSetExp e e' x y i j ⟧ = 𝓒 .isSetHom ⟦ e ⟧ ⟦ e' ⟧ (cong ⟦_⟧ x) (cong ⟦_⟧ y) i j

      sem : Functor FreeCat 𝓒
      sem .Functor.F-ob v = ı $g v 
      sem .Functor.F-hom e = ⟦ e ⟧
      sem .Functor.F-id = refl
      sem .Functor.F-seq e e' = refl
