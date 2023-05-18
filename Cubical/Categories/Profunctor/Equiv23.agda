{-
  Show equivalence of definitions from Profunctor.General
-}

{-# OPTIONS --safe #-}
module Cubical.Categories.Profunctor.Equiv23 where

open import Cubical.Categories.Profunctor.General
open import Cubical.Foundations.Prelude hiding (Path)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function renaming (_∘_ to _∘f_)

open import Cubical.Data.Graph.Base
open import Cubical.Data.Graph.Path
open import Cubical.Data.Sigma.Properties

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Functors.HomFunctor

open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Instances.Functors.More
open import Cubical.Categories.Yoneda.More


open import Cubical.Categories.Equivalence.Base
open import Cubical.Categories.Equivalence.Properties
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Cubical.Categories.NaturalTransformation.More

open import Cubical.Categories.Presheaf.Representable
open import Cubical.Tactics.CategorySolver.Reflection


open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Categories.Presheaf.More

private
  variable ℓC ℓC' ℓD ℓD' ℓs : Level

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} (R : C *-[ ℓs ]-o D)
  (isUnivC : isUnivalent C ) (isUnivD : isUnivalent D) where

  open UnivElt
  open isUniversal
  open isUnivalent
  open Category
  open NatIso
  open isIso
  open NatTrans
  open Functor

  PshFunctorRepresentation≅ParamUniversalElement : Iso (PshFunctorRepresentation C D R) (ParamUniversalElement C D R) 
  PshFunctorRepresentation≅ParamUniversalElement .Iso.fun = PshFunctorRepresentation→ParamUniversalElement C D R
  PshFunctorRepresentation≅ParamUniversalElement .Iso.inv = ParamUniversalElement→PshFunctorRepresentation C D R
  PshFunctorRepresentation≅ParamUniversalElement .Iso.rightInv U = funExt (λ c → {!   !})
  PshFunctorRepresentation≅ParamUniversalElement .Iso.leftInv (G , η) =
    let U' = ((PshFunctorRepresentation→ParamUniversalElement C D R) (G , η)) in
    let (G' , η') = ((ParamUniversalElement→PshFunctorRepresentation C D R) U') in
    -- prove equality of Gs and ηs
    ΣPathP (
      -- prove equality of Gs
      (Functor≡ 
        -- object map is same
        (λ c → refl)
        -- morphisms are the same due to the uniqueness of coinduction
        (λ {x} {y} ϕ →
          let (dx , εx) = (fst (U' x)) in
          let (dy , εy) = (fst (U' y)) in
          let R⟅-,y⟆ = (R ∘F (Id {C = D ^op} ,F Constant (D ^op) C y)) in
          let R⟅dx,-⟆ = ((curryF C (SET _) {Γ = (D ^op)} ⟅ R ⟆)  ⟅ dx ⟆) in
          (G' ⟪ ϕ ⟫)
            ≡⟨ sym((UniversalElement→UnivElt D R⟅-,y⟆ (U' y))
              .universal .is-uniq 
              ((R⟅dx,-⟆ ⟪ ϕ ⟫) εx) 
              (G ⟪ ϕ ⟫)
              -- nested proof that G ⟪ ϕ ⟫ also satisfies this coinduction
              (
                (D [ εy ∘ᴾ⟨ R⟅-,y⟆ ⟩ (G ⟪ ϕ ⟫) ])
                  ≡⟨ (λ i → (D [ εy ∘ᴾ⟨ R⟅-,y⟆ ⟩ ((D .⋆IdL (G ⟪ ϕ ⟫)) (~ i)) ]))⟩
                (D [ εy ∘ᴾ⟨ R⟅-,y⟆ ⟩ ((D .id) ⋆⟨ D ⟩ (G ⟪ ϕ ⟫)) ])
                  ≡⟨ {!!} ⟩
                (D [ εy ∘ᴾ⟨ R⟅-,y⟆ ⟩ ((G ⟪ ϕ ⟫)) ])
                  ≡⟨ 
                    is-uniq-converse ((UniversalElement→UnivElt D R⟅-,y⟆ (U' y)) .universal)
                    (lower ((η .nIso y .inv .N-ob (G ⟅ x ⟆)) (lift  (G ⟪ ϕ ⟫))))
                    (G ⟪ ϕ ⟫ )
                    (λ i → (terminalArrowUnique (Elements D R⟅-,y⟆) {T = U' y} (G ⟪ ϕ ⟫ , {!!})) (~ i) .fst)
                  ⟩
                  -- ⟩
                -- ((η .nIso y .inv .N-ob (G ⟅ x ⟆)) ((λ f → f ⋆⟨ D ⟩ (G ⟪ ϕ ⟫)) (D .id)))
                -- ((η .nIso y .inv .N-ob (G ⟅ x ⟆)) ((D .id) ⋆⟨ D ⟩ (G ⟪ ϕ ⟫)))
                -- ((η .nIso y .inv .N-ob (G ⟅ x ⟆)) ((D .id) ⋆⟨ D ⟩ (G ⟪ ϕ ⟫)))
                lower ((η .nIso y .inv .N-ob (G ⟅ x ⟆)) (lift (G ⟪ ϕ ⟫)))
                  -- naturality of η?
                  ≡⟨ {!terminalArrowUnique (Elements D R⟅-,y⟆) {T = U' y} !} ⟩
                ((((curryF C (SET _) {Γ = (D ^op)} ⟅ R ⟆)  ⟅ (G ⟅ x ⟆) ⟆) ⟪ ϕ ⟫) εx)
                  ≡⟨ refl ⟩
                ((R⟅dx,-⟆ ⟪ ϕ ⟫) εx) ∎
              )
            ) ⟩
          (G ⟪ ϕ ⟫) ∎
        )
      ),
      -- prove equality of ηs
      {!   !}
    )
