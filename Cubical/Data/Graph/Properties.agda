-- Free category over a directed graph/quiver
{-# OPTIONS --safe #-}

module Cubical.Data.Graph.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Graph
open import Cubical.Categories.Category.Base


module _ {ℓv ℓe ℓv' ℓe' ℓv'' ℓe''} {G : Graph ℓv ℓe}{G' : Graph ℓv' ℓe'}{G'' : Graph ℓv'' ℓe''} where
  _⋆GrHom_ : GraphHom G G' → GraphHom G' G'' → GraphHom G G''
  (ϕ ⋆GrHom ψ) ._$g_ = λ z → ψ $g (ϕ $g z)
  (ϕ ⋆GrHom ψ) ._<$g>_ e = ψ <$g> (ϕ <$g> e)
  
