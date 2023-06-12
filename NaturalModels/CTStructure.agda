module NaturalModels.CTStructure where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.FinSet

open import UMP
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism

open Category
open CartesianCategory
open UnivElt
open isUniversal

record CTStructure (ℓ ℓ' ℓt : Level) : Type (ℓ-max (ℓ-suc ℓ)
  (ℓ-max (ℓ-suc ℓ') (ℓ-suc ℓt))) where
  field
    B : CartesianCategory ℓ ℓ'
    Ty : Type ℓt
    sole : Ty → B .cat .ob
open Functor
open NatTrans
open CTStructure
open CartesianFunctor

record CT-Functor {ℓc ℓc' ℓct ℓd ℓd' ℓdt : Level}
       (C : CTStructure ℓc ℓc' ℓct)
       (D : CTStructure ℓd ℓd' ℓdt) : Type (ℓ-max ℓc (ℓ-max ℓc'
         (ℓ-max ℓct (ℓ-max ℓd (ℓ-max ℓd' (ℓ-max ℓdt (ℓ-suc ℓ-zero))))))) where
  field
    F-B  : CartesianFunctor (C .B) (D .B)
    F-Ty : C .Ty → D .Ty
    F-agree : ∀ {A} → CatIso (D .B .cat) (D .sole (F-Ty A))
      (F-B .func .F-ob (C .sole A)) -- D .sole (F-Ty A) ≡
        -- F-B .func .F-ob (C .sole A)
private
  variable
    ℓc ℓc' ℓt ℓt' ℓp : Level

open CT-Functor

CT-Trans : {ℓc ℓc' ℓct ℓd ℓd' ℓdt : Level} {C : CTStructure ℓc ℓc' ℓct}
           {D : CTStructure ℓd ℓd' ℓdt}
           (F G : CT-Functor C D)
         → Type _
CT-Trans F G = NatTrans (F .F-B .func) (G .F-B .func)

-- representability by a type
TypeRepr : ∀ (C : CTStructure ℓc ℓc' ℓt) →
           (P : Presheaf (C .B .cat) ℓp) → Type _
TypeRepr C P = Σ[ A ∈ C .Ty ] PshIso (C .B .cat) (C .B .cat [-, C .sole A ]) P
