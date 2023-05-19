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
    let ηinv = symNatIso η in
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
              -- this works by the following diagram between the presheafs R⟅-,a⟆ and D[-,Ga]
              --              ηx
              --       R⟅-,x⟆ ==> D[-,Gx]
              --  λR(ϕ)  ∥         ∥ (G(ϕ) ∘ -)
              --         ⇓    ηy   ⇓
              --       R⟅-,y⟆ ==> D[-,Gy] 
              --
              -- These are presheafs D ^op ⟶ SET, and we consider the slice of this diagram at G ⟅ x ⟆
              --               ηxᴳˣ 
              --        R⟅Gx,x⟆ --→ D[Gx,Gx]
              -- λR(ϕ)ᴳˣ  |            |  (G(ϕ) ∘ -)
              --          ↓            ↓
              --        R⟅Gx,y⟆ --→ D[Gx,Gy]
              --                ηyᴳˣ
              -- Note that by construction, the η and G here define the coinduction and εx ⋆ maps (these are what form the NatIso)
              -- Thus the equality of the 2 expressions below follows from the fact that η is a natural transformation
              -- 
              --                      εx ⋆ 
              --            D[Gx,Gx] ---→ R⟅Gx,x⟆
              --             |  id   ⊢→ εx  |  
              -- (G(ϕ) ∘ -)  |   ↓       ↓  |  λR(ϕ)ᴳˣ = R⟅Gx,-⟆ ⟪ ϕ ⟫
              --             ↓  G(ϕ) ⊢→  ∎  ↓
              --            D[Gx,Gy] --→ R⟅Gx,y⟆
              --                     εy ⋆
              (
                (D [ εy ∘ᴾ⟨ R⟅-,y⟆ ⟩ (G ⟪ ϕ ⟫) ])
                  ≡⟨ refl ⟩
                (D [ lower ((ηinv .trans .N-ob y .N-ob (G ⟅ y ⟆)) (lift (D .id))) ∘ᴾ⟨ R⟅-,y⟆ ⟩ (G ⟪ ϕ ⟫) ])
                  ≡⟨ refl ⟩
                (R⟅-,y⟆ ⟪ G ⟪ ϕ ⟫ ⟫) (lower ((ηinv .trans .N-ob y .N-ob (G ⟅ y ⟆)) (lift (D .id))))
                  ≡⟨ {!λ i → ((ηinv .trans .N-ob y .N-hom (G ⟪ ϕ ⟫ )) (~ i)) (lift (D .id)) !} ⟩
                ((R⟅dx,-⟆ ⟪ ϕ ⟫) εx) ∎
              )
            ) ⟩
          (G ⟪ ϕ ⟫) ∎
        )
      ),
      -- prove equality of ηs
      {!   !}
    )
