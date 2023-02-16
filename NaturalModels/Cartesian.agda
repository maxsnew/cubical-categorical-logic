module NaturalModels.Cartesian where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors

-- Three levels are for:
--  ℓo: type of contexts/objects
--  ℓt: type of substitutions/terms
record SimplyTypedCategory (ℓo ℓt : Level) : Type ((ℓ-max (ℓ-suc ℓo) (ℓ-suc ℓt))) where
  open Category
  field
    -- A cartesian category B of contexts and substitutions
    B    : Category ℓo ℓt
    ·    : Terminal B
    _,,_ : BinProducts B
    -- a type of objects and for each object a presheaf of terms for that object
    Ob   : Type ℓo
    Tm   : ∀ (A : Ob) → Functor (B ^op) (SET ℓt)
    -- Tm A is always representable, this defines a context containing a single variable
    Tm-repr : ∀ (A : Ob) → Σ[ x:A ∈ B .ob ] CatIso (FUNCTOR (B ^op) (SET ℓt))  (Tm A) ( B [-, x:A ])
