module NaturalModels.Cartesian.Instances where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Representable

open import NaturalModels.Cartesian
open import UMP

private
  variable
    ℓ ℓ' : Level

open Category
open CartesianCategory
open SimplyTypedCategory
open UnivElt
open isUniversal

self : (C : CartesianCategory ℓ ℓ') → SimplyTypedCategory ℓ ℓ' ℓ ℓ'
self C .B = C
self C .Ty = C .cat .ob
self C .Tm = λ a → C .cat [-, a ]
self C .Tm-repr A .vertex = A
self C .Tm-repr A .element = C .cat .id
self C .Tm-repr A .universal .coinduction f = f
self C .Tm-repr A .universal .commutes f = C .cat .⋆IdR _
self C .Tm-repr A .universal .is-uniq g f fid≡g =
  f ≡⟨ sym (C .cat .⋆IdR f) ⟩ fid≡g
