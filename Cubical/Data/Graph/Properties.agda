-- Free category over a directed graph/quiver
{-# OPTIONS --safe #-}

module Cubical.Data.Graph.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Graph
open import Cubical.Categories.Category.Base


module _ {ℓv ℓe ℓv' ℓe' ℓv'' ℓe''}
         {G : Graph ℓv ℓe}{G' : Graph ℓv' ℓe'}{G'' : Graph ℓv'' ℓe''} where
  _⋆GrHom_ : GraphHom G G' → GraphHom G' G'' → GraphHom G G''
  (ϕ ⋆GrHom ψ) ._$g_ = λ z → ψ $g (ϕ $g z)
  (ϕ ⋆GrHom ψ) ._<$g>_ e = ψ <$g> (ϕ <$g> e)

  _∘GrHom_ : GraphHom G' G'' → GraphHom G G' → GraphHom G G''
  ψ ∘GrHom ϕ = ϕ ⋆GrHom ψ

IdHom : ∀ {ℓv ℓe} {G : Graph ℓv ℓe} → GraphHom G G
IdHom {G} ._$g_ = λ z → z
IdHom {G} ._<$g>_ = λ z → z

GrHom≡ : ∀ {ℓg ℓg' ℓh ℓh'}
           {G : Graph ℓg ℓg'}{H : Graph ℓh ℓh'} {ϕ ψ : GraphHom G H}
       → (h : ∀ v → ϕ $g v ≡ ψ $g v)
       → (∀ {v w} (e : G .Edge v w)
       → PathP (λ i → H .Edge (h v i) (h w i)) (ϕ <$g> e) (ψ <$g> e))
       → ϕ ≡ ψ
GrHom≡ h k i $g x = h x i
GrHom≡ h k i <$g> x = k x i
