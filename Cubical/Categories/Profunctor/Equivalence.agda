{-
  Show equivalence of definitions from Profunctor.General
-}

{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Profunctor.Equivalence where

open import Cubical.Categories.Profunctor.General

open import Cubical.Foundations.Prelude hiding (Path)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Path
open import Cubical.Foundations.Function renaming (_∘_ to _∘f_)
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Graph.Base
open import Cubical.Data.Graph.Path
open import Cubical.Data.Sigma.Properties

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.Elements
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Limits.Terminal

open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Instances.Functors.More
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Presheaf.More

open import Cubical.Tactics.CategorySolver.Reflection
open import Cubical.Tactics.FunctorSolver.Reflection




private
  variable ℓC ℓC' ℓD ℓD' ℓs : Level

module _ (C : Category ℓC ℓC') (D : Category ℓD ℓD') (R : C *-[ ℓs ]-o D) where

  open Category
  open NatIso
  open NatTrans
  open Functor

  PshFunctorRepresentation≅ProfRepresentation : Iso (PshFunctorRepresentation C D R) (ProfRepresentation C D R)
  PshFunctorRepresentation≅ProfRepresentation =
    record {
      fun = PshFunctorRepresentation→ProfRepresentation C D R;
      inv = ProfRepresentation→PshFunctorRepresentation C D R;
      rightInv = Prof→Psh→Prof;
      leftInv = Psh→Prof→Psh
    }
    where
    Prof→Psh→Prof : (Prof : ProfRepresentation C D R)
        → (PshFunctorRepresentation→ProfRepresentation C D R)
          ((ProfRepresentation→PshFunctorRepresentation C D R) Prof
          ) ≡ Prof
    Prof→Psh→Prof (G , η) =
      let (G' , η') = (PshFunctorRepresentation→ProfRepresentation C D R) ((ProfRepresentation→PshFunctorRepresentation C D R) (G , η)) in
      let G≡G' = Functor≡ (λ _ → refl) (λ _ → refl) in
        ΣPathP (G≡G' ,
          makeNatIsoPathP
            refl
            (cong′ (λ X → (LiftF ∘F (Functor→Prof*-o C D X))) G≡G')
            (funExt λ (d , c) →
              funExt λ _ → refl
            )
        )
    Psh→Prof→Psh : (Psh : PshFunctorRepresentation C D R)
      → (ProfRepresentation→PshFunctorRepresentation C D R)
        ((PshFunctorRepresentation→ProfRepresentation C D R) Psh
        ) ≡ Psh
    Psh→Prof→Psh (G , η) =
      let (G' , η') = (ProfRepresentation→PshFunctorRepresentation C D R) ((PshFunctorRepresentation→ProfRepresentation C D R) (G , η)) in
      let G≡G' = Functor≡ (λ _ → refl) (λ _ → refl) in
          ΣPathP (G≡G' ,
            makeNatIsoPathP refl (cong′ (λ X → (Prof*-o→Functor C D) (LiftF ∘F (Functor→Prof*-o C D X))) G≡G')
            (funExt (λ (c : C .ob) →
              makeNatTransPathP
                refl
                (cong′ (λ X → (Prof*-o→Functor C D (LiftF {ℓD'}{ℓs} ∘F (Functor→Prof*-o C D X))) .F-ob c) G≡G')
                (funExt (λ (d : D .ob) →
                  funExt λ _ → refl
                ))
              ))
          )

  open Contravariant
  open UnivElt
  open isUniversal

  PshFunctorRepresentation≅ParamUniversalElement : Iso (PshFunctorRepresentation C D R) (ParamUniversalElement C D R)
  PshFunctorRepresentation≅ParamUniversalElement =
    record {
      fun = PshFunctorRepresentation→ParamUniversalElement C D R ;
      inv = ParamUniversalElement→PshFunctorRepresentation C D R ;
      rightInv = Universal→PshFunctor→Universal ;
      leftInv = PshFunctor→Universal→PshFunctor
    }
    where
    Universal→PshFunctor→Universal : ∀ (U : ParamUniversalElement C D R) →
      ((PshFunctorRepresentation→ParamUniversalElement C D R)
        ((ParamUniversalElement→PshFunctorRepresentation C D R) U) ≡
      U)
    Universal→PshFunctor→Universal U =
      let (G , η) = (ParamUniversalElement→PshFunctorRepresentation C D R) U
          η⁻¹ = symNatIso η
          U' = PshFunctorRepresentation→ParamUniversalElement C D R (G , η)
      in
      funExt (λ c →
        let εc = (U c) .fst .snd
            ε'c = (U' c) .fst .snd
            R⟅-,c⟆ = R ∘F (Id {C = D ^op} ,F Constant (D ^op) C c)
        in
        ΣPathPProp
          (isPropIsTerminal (∫ᴾ_ {C = D} R⟅-,c⟆))
          (ΣPathP (
            -- same object
            refl ,
            -- paths equal as εc ⋆ id = εc
            (ε'c ≡⟨ (λ i → (R⟅-,c⟆ .F-id (i)) εc) ⟩ εc ∎)
          ))
      )

    PshFunctor→Universal→PshFunctor : ∀ (Psh : (PshFunctorRepresentation C D R)) →
      ((ParamUniversalElement→PshFunctorRepresentation C D R)
        ((PshFunctorRepresentation→ParamUniversalElement C D R) Psh) ≡
      Psh)
    PshFunctor→Universal→PshFunctor (G , η) =
      let η⁻¹ = symNatIso η
          U' = ((PshFunctorRepresentation→ParamUniversalElement C D R) (G , η))
          (G' , η') = ((ParamUniversalElement→PshFunctorRepresentation C D R) U')
          -- prove equality of Gs
          G'≡G = (Functor≡
                    -- object map is same
                    (λ c → refl)
                    -- morphisms are the same due to the uniqueness of coinduction
                    (λ {x} {y} ϕ →
                      let (dx , εx) = (fst (U' x))
                          (dy , εy) = (fst (U' y))
                          R⟅-,y⟆ = (R ∘F (Id {C = D ^op} ,F Constant (D ^op) C y))
                          R⟅dx,-⟆ = ((curryF C (SET _) {Γ = (D ^op)} ⟅ R ⟆)  ⟅ dx ⟆)
                          p = ((((G ⟪ ϕ ⟫) ⋆⟨ D ⟩ D .id) ⋆⟨ D ⟩ G ⟪ C .id ⟫)
                                ≡⟨ solveFunctor! C D G ⟩
                               ((D .id ⋆⟨ D ⟩ D .id) ⋆⟨ D ⟩ (G ⟪ ϕ ⟫)) ∎
                              )
                      in
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
                              lower (η⁻¹ .trans .N-ob y .N-ob (G ⟅ x ⟆) (lift (p i)))
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
                        )) ⟩
                      (G ⟪ ϕ ⟫) ∎
                    )
                 )
            in
            ΣPathP (
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
                      (funExt λ _ → refl)
                    ))
                  )
                ))
              )
            )
