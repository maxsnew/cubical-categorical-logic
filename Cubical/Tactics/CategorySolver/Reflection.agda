{-# OPTIONS --safe #-}

module Cubical.Tactics.CategorySolver.Reflection where

open import Cubical.Foundations.Prelude

open import Agda.Builtin.Reflection hiding (Type)
open import Agda.Builtin.String

open import Cubical.Data.Bool
open import Cubical.Data.List
open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Reflection.Base

open import Cubical.Categories.Category
open import Cubical.Tactics.CategorySolver.Solver

private
  variable
    ℓ ℓ' : Level

module ReflectionSolver where
  module _ (category : Term) where
    pattern category-args xs =
      _ h∷ _ h∷ _ v∷ xs

    pattern “id” =
      def (quote Category.id) (category-args (_ h∷ []))

    pattern “⋆” f g =
      def (quote Category._⋆_) (category-args (_ h∷ _ h∷ _ h∷ f v∷ g v∷ []))

    -- Parse the input into an exp
    buildExpression : Term → Term
    buildExpression “id” = con (quote idₑ) []
    buildExpression (“⋆” f g) = con (quote _⋆ₑ_) (buildExpression f v∷ buildExpression g v∷ [])
    buildExpression f = con (quote ↑_) (f v∷ [])

  record CatNames : Type where
    field
      is-⋆ : Name → Bool
      is-id : Name → Bool

  -- | TODO: idk why these can't just be shared
  _==_ = primQNameEquality
  {-# INLINE _==_ #-}

  {-
    `getLastTwoArgsOf` maps a term 'def n (z₁ ∷ … ∷ zₙ ∷ x ∷ y ∷ [])' to the pair '(x,y)'
    non-visible arguments are ignored.
  -}
  getLastTwoArgsOf : Name → Term → Maybe (Term × Term)
  getLastTwoArgsOf n' (def n xs) =
    if n == n'
    then go xs
    else nothing
      where
      go : List (Arg Term) → Maybe (Term × Term)
      go (varg x ∷ varg y ∷ []) = just (x , y)
      go (x ∷ xs)               = go xs
      go _                      = nothing
  getLastTwoArgsOf n' _ = nothing

  {-
    `splitEquation` maps a term 'x ≡ y' to the pair '(x,y)'
  -}
  splitEquation : Term → Maybe (Term × Term)
  splitEquation = getLastTwoArgsOf (quote PathP)

  solve-macro : Term -- ^ The term denoting the category
              → Term -- ^ The hole whose goal should be an equality between morphisms in the category
              → TC Unit
  solve-macro category hole =
    do
      -- | First we normalize the goal
      goal ← inferType hole >>= normalise
      -- | Then we parse the goal into an AST
      just (lhs , rhs) ← returnTC (map-Maybe (map-× (buildExpression category) (buildExpression category)) (splitEquation goal))
        where
          nothing
            → typeError(strErr "The cat solver didn't work. It's Max S. New's fault, though he probably doesn't understand why tbh" ∷ termErr goal ∷ [])
      -- | Then we invoke the solver
      -- | And we unify the result of the solver with the original hole.
      unify hole (def (quote solve ) (harg {q = quantity-ω} unknown ∷ harg {q = quantity-ω} unknown ∷ -- levels of the category
                                      category v∷
                                      harg {q = quantity-ω} unknown ∷ harg {q = quantity-ω} unknown ∷ -- domain/codomain of the morphisms
                                      lhs v∷ rhs v∷
                                      def (quote refl) [] v∷ [])
                                      )
macro
  solveCat! : Term → Term → TC _
  solveCat! = ReflectionSolver.solve-macro
