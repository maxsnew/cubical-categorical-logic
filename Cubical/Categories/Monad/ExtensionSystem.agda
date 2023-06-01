{-
   Monads as extension systems, i.e., in terms of unit and bind, deriving the rest of the structure
   https://ncatlab.org/nlab/show/extension+system
-}
{-# OPTIONS --safe #-}
module Cubical.Categories.Monad.ExtensionSystem where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor renaming (𝟙⟨_⟩ to funcId)
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.NaturalTransformation.Properties
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Constructions.BinProduct

private
  variable
    ℓ ℓ' : Level

module _ (C : Category ℓ ℓ') where
  open Category
  private
    variable
      a b c : C .ob
      f g h : C [ a , b ]

  record ExtensionSystem (T : C .ob → C .ob) : Type (ℓ-max ℓ ℓ') where
    field
      η : C [ a , T a ]
      bind : C [ a , T b ] → C [ T a , T b ]
      bind-r : bind (η {a = a}) ≡ C .id
      bind-l : bind f ∘⟨ C ⟩ η ≡ f
      bind-comp : bind f ∘⟨ C ⟩ bind g ≡ bind (bind f ∘⟨ C ⟩ g)

  module _ {T} (E : ExtensionSystem T) where
    open ExtensionSystem E
    Kleisli : Category _ _
    Kleisli .ob = C .ob
    Kleisli .Hom[_,_] a b = C [ a , T b ]
    Kleisli .id = η
    Kleisli ._⋆_ f g = bind g ∘⟨ C ⟩ f
    Kleisli .⋆IdL f = bind-l
    Kleisli .⋆IdR f = cong₂ (comp' C) bind-r refl ∙ C .⋆IdR f
    Kleisli .⋆Assoc f g h = C .⋆Assoc _ _ _ ∙ cong₂ (comp' C) bind-comp refl
    Kleisli .isSetHom = C .isSetHom

    open Functor
    G : Functor Kleisli C
    G .F-ob = T
    G .F-hom = bind
    G .F-id = bind-r
    G .F-seq f g = sym bind-comp

    open import Cubical.Categories.Adjoint.UniversalElements
    open import Cubical.Categories.Presheaf.Representable
    open UnivElt
    open isUniversal
    F : LeftAdjoint _ _ G
    F c .vertex = c
    F c .element = η
    F c .universal .coinduction = λ z → z
    F c .universal .commutes ϕ = bind-l
    F c .universal .is-uniq ϕ f p = sym bind-l ∙ p

    -- TODO: by abstract nonsense construct a monad structure for T
