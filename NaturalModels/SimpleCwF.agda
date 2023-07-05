module NaturalModels.SimpleCwF where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Data.Sigma
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.Representable

open Category
SCwF : (ℓ ℓ' ℓ'' ℓ''' : Level)
     → Type (ℓ-max (ℓ-max (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
            (ℓ-suc ℓ'')) (ℓ-suc ℓ'''))
SCwF ℓ ℓ' ℓ'' ℓ''' =
  -- The category of contexts and substitutions
  Σ[ C ∈ Category ℓ ℓ' ]
  -- With a terminal object (empty context)
  Terminal C ×
  -- A type of syntactic types
  (Σ[ Ty ∈ Type ℓ'' ]
  -- A presheaf of terms for each type
  Σ[ Tm ∈ (∀ (A : Ty) → Presheaf C ℓ''') ]
  -- Such that the base category has products with terms (context extension)
  (∀ (Γ : C .ob) (A : Ty)
  → UnivElt C (×Sets ∘F (LiftF {ℓ' = ℓ'''} ∘F ((C [-, Γ ])) ,F
                         LiftF {ℓ' = ℓ'} ∘F Tm A))))

