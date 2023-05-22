{-
  Show equivalence of definitions from Profunctor.General
-}

{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Profunctor.Equiv23 where

open import Cubical.Categories.Profunctor.General
open import Cubical.Foundations.Prelude hiding (Path)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Path
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
open import Cubical.Categories.Isomorphism
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
open import Cubical.Tactics.FunctorSolver.Reflection

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
  PshFunctorRepresentation≅ParamUniversalElement .Iso.rightInv U = funExt (λ c → {!  pathToIso-Square !})
  PshFunctorRepresentation≅ParamUniversalElement .Iso.leftInv (G , η) =
    -- prove equality of Gs and ηs
    ΣPathP (
      -- prove equality of Gs
      G'≡G ,
      -- prove equality of ηs
      (makeNatIsoPathP 
        refl
        (cong′ (λ X → Prof*-o→Functor C D (LiftF {ℓD'}{ℓs} ∘F Functor→Prof*-o C D X)) G'≡G)
        (funExt (λ (c : C .ob) →
          (makeNatTransPathP 
            refl 
            (cong′ (λ X → (Prof*-o→Functor C D (LiftF {ℓD'}{ℓs} ∘F Functor→Prof*-o C D X)) .F-ob c) G'≡G)
            (funExt (λ (d : D .ob) →
              (pathToIso-Square {C = (SET _)}
                {x = (Prof*-o→Functor C D (LiftF {ℓs}{ℓD'} ∘F R)) .F-ob c .F-ob d}
                {y = (Prof*-o→Functor C D (LiftF {ℓs}{ℓD'} ∘F R)) .F-ob c .F-ob d}
                {z = (Prof*-o→Functor C D (LiftF {ℓD'}{ℓs} ∘F Functor→Prof*-o C D G')) .F-ob c .F-ob d}
                {w = (Prof*-o→Functor C D (LiftF {ℓD'}{ℓs} ∘F Functor→Prof*-o C D G)) .F-ob c .F-ob d}
                refl 
                (cong′ (λ X → (Prof*-o→Functor C D (LiftF {ℓD'}{ℓs} ∘F Functor→Prof*-o C D X)) .F-ob c .F-ob d) G'≡G)
                (η' .trans .N-ob c .N-ob d)
                (η .trans .N-ob c .N-ob d)
                (funExt (λ ϕ →
                  {-
                    final piece of the puzzle. show the that these paths behave.
                    refl should reduce to id, but still need to work through some details
                    here
                                  η'ᶜᵈ
                      ϕ ∈ R(d,c) ---→ D[d,G'c]
                            |              |
                    (refl)  |              | G'≡G lifted via cong′
                            ↓              ↓
                          R(d,c) ---→ D[d,Gc]
                                  ηᶜᵈ
                  -}
                  ((pathToIso {C = (SET _)} (λ i → (Prof*-o→Functor C D (LiftF {ℓD'}{ℓs} ∘F (Functor→Prof*-o C D (G'≡G i)))) .F-ob c .F-ob d) .fst) ((η' .trans .N-ob c .N-ob d) ϕ))
                    ≡⟨ {!   !} ⟩
                  ((η .trans .N-ob c .N-ob d) ((pathToIso {C = (SET _)} (λ _ → (Prof*-o→Functor C D (LiftF {ℓs}{ℓD'} ∘F R)) .F-ob c .F-ob d) .fst) ϕ)) ∎
                ))
              )
            ))
          )
        ))
      )
    )
    where
    η⁻¹ = symNatIso η
    U' = ((PshFunctorRepresentation→ParamUniversalElement C D R) (G , η))
    G',η' = ((ParamUniversalElement→PshFunctorRepresentation C D R) U')
    η' = snd G',η'
    G' = fst G',η'
    G'≡G = (Functor≡
        -- object map is same
        (λ c → refl)
        -- morphisms are the same due to the uniqueness of coinduction
        (λ {x} {y} ϕ →
          let (dx , εx) = (fst (U' x)) in
          let (dy , εy) = (fst (U' y)) in
          let R⟅-,y⟆ = (R ∘F (Id {C = D ^op} ,F Constant (D ^op) C y)) in
          let R⟅dx,-⟆ = ((curryF C (SET _) {Γ = (D ^op)} ⟅ R ⟆)  ⟅ dx ⟆) in
          let p = ((((G ⟪ ϕ ⟫) ⋆⟨ D ⟩ D .id) ⋆⟨ D ⟩ G ⟪ C .id ⟫) ≡⟨ solveFunctor! C D G ⟩ ((D .id ⋆⟨ D ⟩ D .id) ⋆⟨ D ⟩ (G ⟪ ϕ ⟫)) ∎) in
          (G' ⟪ ϕ ⟫)
            ≡⟨ sym((UniversalElement→UnivElt D R⟅-,y⟆ (U' y))
              .universal .is-uniq
              ((R⟅dx,-⟆ ⟪ ϕ ⟫) εx)
              (G ⟪ ϕ ⟫)
              {-
                nested proof that G ⟪ ϕ ⟫ also satisfies this coinduction
                this works by the following diagram between the presheafs R⟅-,a⟆ and D[-,Ga]
                             ηx
                      R⟅-,x⟆ ==> D[-,Gx]
                 λR(ϕ)  ∥         ∥ (G(ϕ) ∘ -)
                        ⇓    ηy   ⇓
                      R⟅-,y⟆ ==> D[-,Gy]

                These are presheafs D ^op ⟶ SET, and we consider the slice of this diagram at G ⟅ x ⟆
                              ηxᴳˣ
                       R⟅Gx,x⟆ --→ D[Gx,Gx]
                λR(ϕ)ᴳˣ  |            |  (G(ϕ) ∘ -)
                         ↓            ↓
                       R⟅Gx,y⟆ --→ D[Gx,Gy]
                               ηyᴳˣ
                Note that by construction, the η and G here define the coinduction and εx ⋆ maps (these are what form the NatIso)
                Thus the equality of the 2 expressions below follows from the fact that η is a natural transformation

                                     εx ⋆
                           D[Gx,Gx] ---→ R⟅Gx,x⟆
                            |  id   ⊢→ εx  |
                (G(ϕ) ∘ -)  |   ↓       ↓  |  λR(ϕ)ᴳˣ = R⟅Gx,-⟆ ⟪ ϕ ⟫
                            ↓  G(ϕ) ⊢→  ∎  ↓
                           D[Gx,Gy] --→ R⟅Gx,y⟆
                                    εy ⋆
              -}
              (
                (D [ εy ∘ᴾ⟨ R⟅-,y⟆ ⟩ (G ⟪ ϕ ⟫) ])
                  ≡⟨ refl ⟩
                lower (((LiftF ∘F R⟅-,y⟆) ⟪ G ⟪ ϕ ⟫ ⟫) ((η⁻¹ .trans .N-ob y .N-ob (G ⟅ y ⟆)) (lift (D .id))))
                  -- since εy is defined in terms of R(Gy, y), we first use naturality
                  -- to consider the relevant component of the εy ⋆ map, namely the component at Gx
                  ≡⟨ (λ i → lower (((η⁻¹ .trans .N-ob y .N-hom (G ⟪ ϕ ⟫)) (~ i)) (lift (D .id)) ) ) ⟩
                lower ((η⁻¹ .trans .N-ob y .N-ob (G ⟅ x ⟆)
                  (lift (((G ⟪ ϕ ⟫) ⋆⟨ D ⟩ D .id) ⋆⟨ D ⟩ G ⟪ C .id ⟫)))
                )
                  -- next, we use some recombining of G ϕ to see it as an application
                  -- of a different Hom Functor applied to id at Gx instead of Gy:
                  ≡⟨ (λ i →
                    lower (η⁻¹ .trans .N-ob y .N-ob (G ⟅ x ⟆)
                      (lift (p i))
                    )
                  ) ⟩
                lower (η⁻¹ .trans .N-ob y .N-ob (G ⟅ x ⟆)
                  (lift ((D .id ⋆⟨ D ⟩ D .id) ⋆⟨ D ⟩ (G ⟪ ϕ ⟫)))
                )
                  ≡⟨ refl ⟩
                lower (
                  ((((Prof*-o→Functor C D (LiftF ∘F (HomFunctor D  ∘F (Id {C = D ^op} ×F G)))) ⟪ ϕ ⟫)
                    ⋆⟨ FUNCTOR (D ^op) (SET _) ⟩
                  η⁻¹ .trans .N-ob y) .N-ob (G ⟅ x ⟆))
                  (lift (D .id))
                )
                  -- now, since we are operating of the section of Gx as described above, we
                  -- can use the above argument to port over to εx
                  ≡⟨ (λ i → lower (
                    (((η⁻¹ .trans .N-hom ϕ) (i)) .N-ob (G ⟅ x ⟆))
                    (lift (D .id))
                  )) ⟩
                lower (
                  ((η⁻¹ .trans .N-ob x
                    ⋆⟨ FUNCTOR (D ^op) (SET _) ⟩
                  ((Prof*-o→Functor C D (LiftF ∘F R)) ⟪ ϕ ⟫)
                  ) .N-ob (G ⟅ x ⟆))
                  (lift (D .id))
                )
                  ≡⟨ refl ⟩
                ((R⟅dx,-⟆ ⟪ ϕ ⟫) εx) ∎
              )
            ) ⟩
          (G ⟪ ϕ ⟫) ∎
        )
      )
