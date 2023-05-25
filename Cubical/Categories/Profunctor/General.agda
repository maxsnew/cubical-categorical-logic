{-

  Definition of profunctors (https://ncatlab.org/nlab/show/profunctor)
  and some basic facts about them.

  We define a profunctor C ⊶ D as a functor C^o x D -> Set. We pick
  the universe levels such that the hom sets of C and D match Set,
  which roughly matches the set-theoretic notion of "locally small"
  categories.

  We give some convenient notation for thinking of profunctors as a
  notion of "heteromorphism" between objects of different categories,
  with appropriate composition.

  A main use of profunctors is in defining universal properties as
  profunctors representable as a functor. The first definition is the
  isomorphism Hom[ F - , = ] =~ R[ - , = ] and the second is a
  generalization of the definition of an adjoint by giving "universal
  morphisms". These notions are equivalent, though for now we have
  only shown logical equivalence.

-}

{-# OPTIONS --safe #-}
module Cubical.Categories.Profunctor.General where

open import Cubical.Foundations.Prelude hiding (Path)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function renaming (_∘_ to _∘f_)

open import Cubical.Data.Graph.Base
open import Cubical.Data.Graph.Path

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Functors.More
open import Cubical.Categories.Functors.HomFunctor

open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Instances.Functors.More


open import Cubical.Categories.Equivalence.Base
open import Cubical.Categories.Equivalence.Properties
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Yoneda.More

open import Cubical.Categories.Presheaf.More
open import Cubical.Tactics.CategorySolver.Reflection
open import Cubical.Tactics.FunctorSolver.Reflection
open import Cubical.Categories.Constructions.BinProduct.More


open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Categories.Presheaf.More

-- There are possibly 5 different levels to consider: the levels of
-- objects and arrows of the two different categories and the level of
-- the sets in the profunctor.

private
  variable
    ℓC ℓC' ℓD ℓD' : Level
PROFo-* : (C : Category ℓC ℓC') (D : Category ℓD ℓD') → ∀ ℓS → Category _ _
PROFo-* C D ℓS = FUNCTOR (C ^op ×C D) (SET ℓS)

PROF⊶ = PROFo-*

PROF*-o : (D : Category ℓD ℓD')(C : Category ℓC ℓC') → ∀ ℓS → Category _ _
PROF*-o D C = PROFo-* C D

PROF⊷ = PROF*-o

_o-[_]-*_ : (C : Category ℓC ℓC') → ∀ ℓS → (D : Category ℓD ℓD') → Type _
C o-[ ℓS ]-* D = Category.ob (PROF⊶ C D ℓS)

_*-[_]-o_ : (C : Category ℓC ℓC') → ∀ ℓS → (D : Category ℓD ℓD') → Type _
C *-[ ℓS ]-o D = D o-[ ℓS ]-* C

private
  variable
    ℓs : Level

open Functor

Functor→Prof*-o : (C : Category ℓC ℓC') (D : Category ℓD ℓD') (F : Functor C D) → C *-[ ℓD' ]-o D
Functor→Prof*-o C D F = HomFunctor D ∘F (Id {C = D ^op} ×F F)

Functor→Profo-* : (C : Category ℓC ℓC') (D : Category ℓD ℓD') (F : Functor C D) → C o-[ ℓD' ]-* D
Functor→Profo-* C D F = HomFunctor D ∘F ((F ^opF) ×F Id {C = D})

Prof*-o→Functor : (C : Category ℓC ℓC') (D : Category ℓD ℓD') (R : C *-[ ℓs ]-o D) → Functor C (FUNCTOR (D ^op) (SET ℓs))
Prof*-o→Functor C D R = curryFl (D ^op) (SET _) ⟅ R ⟆

Profo-*→Functor : (C : Category ℓC ℓC') (D : Category ℓD ℓD') (R : C o-[ ℓs ]-* D) → Functor (C ^op) (FUNCTOR D (SET ℓs))
Profo-*→Functor C D R = curryF D (SET _) ⟅ R ⟆

module _ (C : Category ℓC ℓC') (D : Category ℓD ℓD') where
  open Category

  -- | Note that this works for both *-o and o-*, either way, the
  -- | contravariant variable goes on the left, to match Hom.
  _p[_,_] : ∀ {ℓs} → (C *-[ ℓs ]-o D) → D .ob → C .ob → Type ℓs
  R p[ d , c ] = ⟨ R ⟅ d , c ⟆ ⟩

  module _ {ℓs} (R : C *-[ ℓs ]-o D) where
    ProfRepresents : (Functor C D) → Type _
    ProfRepresents G = NatIso (LiftF {ℓs}{ℓD'} ∘F R) (LiftF {ℓD'}{ℓs} ∘F Functor→Prof*-o C D G)

    -- | Definition 1: A profunctor R representation is a functor G
    -- | with a natural isomorphism between R and G viewed as a profunctor
    ProfRepresentation : Type _
    ProfRepresentation = Σ[ G ∈ Functor C D ] ProfRepresents G

    -- | Definition 2: A profunctor R representation is a functor G
    -- | with a natural isomorphism between λF R and Y o G.
    PshFunctorRepresentation : Type _
    PshFunctorRepresentation =
      Σ[ G ∈ Functor C D ]
      NatIso (Prof*-o→Functor C D (LiftF {ℓs}{ℓD'} ∘F R))
             (Prof*-o→Functor C D (LiftF {ℓD'}{ℓs} ∘F Functor→Prof*-o C D G))

    -- | Definition 3: Parameterized Universal Element
    -- | A profunctor R representation is a *function* from objects (c : C) to universal elements for R [-, c ]
    ParamUniversalElement : Type _
    ParamUniversalElement = (c : C .ob) → UniversalElement D (R ∘F (Id {C = D ^op} ,F Constant (D ^op) C c))

    -- | Definition 4: Parameterized UnivElt
    -- | Same but with the unpacked UnivElt definition
    ParamUnivElt : Type _
    ParamUnivElt = (c : C .ob) → UnivElt D (R ∘F (Id {C = D ^op} ,F Constant (D ^op) C c))

    -- Show equivalence of all four definitions.
    -- Here we provide functions between definitions,
    -- we offload the proofs that these are indeed equivalences to Profunctor.Equivalence

    -- | Definition 1 → Definition 2
    ProfRepresentation→PshFunctorRepresentation : ProfRepresentation → PshFunctorRepresentation
    ProfRepresentation→PshFunctorRepresentation (G , η) = (G ,
        (preservesNatIsosF (curryFl (D ^op) (SET _)) η)
      )

    open isEquivalence
    open NatIso
    open isWeakEquivalence

    -- | Definition 2 → Definition 1
    PshFunctorRepresentation→ProfRepresentation : PshFunctorRepresentation → ProfRepresentation
    PshFunctorRepresentation→ProfRepresentation (G , η) = (G ,
      FUNCTORIso→NatIso (D ^op ×C C) (SET _)
        (liftIso {F = curryFl (D ^op) (SET _) {Γ = C}}
        (isEquiv→isWeakEquiv (curryFl-isEquivalence (D ^op) (SET _) {Γ = C}) .fullfaith)
        (NatIso→FUNCTORIso C _ η)
      ))

    open isIso
    open NatTrans
    open UnivElt
    open isUniversal

    -- TODO fork Functors.Constant and generalize
    -- | Definition 2 → Definition 3
    PshFunctorRepresentation→ParamUniversalElement : PshFunctorRepresentation → ParamUniversalElement
    PshFunctorRepresentation→ParamUniversalElement (G , η) = (λ c →
      let R⟅-,c⟆ = (R ∘F (Id {C = D ^op} ,F Constant (D ^op) C c)) in
      let η⁻¹ = symNatIso η in
        UnivElt→UniversalElement D R⟅-,c⟆ record {
          vertex = (G ⟅ c ⟆) ;
          element = lower ((η⁻¹ .trans .N-ob c .N-ob (G ⟅ c ⟆)) (lift (D .id))) ;
          universal = record {
            coinduction = λ {d} ϕ → lower ((η .trans .N-ob c .N-ob d) (lift ϕ));
            commutes = (λ {d} ϕ →
              let coindϕ = (lower ((η .trans .N-ob c .N-ob d) (lift ϕ))) in
              let p = ((coindϕ ⋆⟨ D ⟩ (D .id)) ⋆⟨ D ⟩ (G ⟪ C .id ⟫) ≡⟨ solveFunctor! C D G ⟩ coindϕ ∎) in
              lower (((LiftF ∘F R⟅-,c⟆) ⟪ coindϕ ⟫) ((η⁻¹ .trans .N-ob c .N-ob (G ⟅ c ⟆)) (lift (D .id))))
                ≡⟨ (λ i → lower ((((η⁻¹ .trans .N-ob c .N-hom coindϕ) (~ i)) (lift (D .id))))) ⟩
              lower ((η⁻¹ .trans .N-ob c .N-ob d) (lift ((coindϕ ⋆⟨ D ⟩ (D .id)) ⋆⟨ D ⟩ (G ⟪ C .id ⟫))))
                ≡⟨ (λ i → lower ((η⁻¹ .trans .N-ob c .N-ob d) (lift ((p i))) )) ⟩
              lower ((η⁻¹ .trans .N-ob c .N-ob d) (lift (coindϕ)))
                ≡⟨ (λ i → lower ((((η .nIso c .ret) (i)) .N-ob d) (lift ϕ))) ⟩
              ϕ ∎) ;
            is-uniq =
              λ {d} ϕ f ε⋆f≡ϕ →
              let coindϕ = (lower ((η .trans .N-ob c .N-ob d) (lift ϕ))) in
              let p = ((f ⋆⟨ D ⟩ (D .id)) ⋆⟨ D ⟩ (G ⟪ C .id ⟫) ≡⟨ solveFunctor! C D G ⟩ f ∎) in
                f
                  ≡⟨ (λ i → lower(((η .nIso c .sec) (~ i) .N-ob d) (lift f))) ⟩
                (lower ((η .trans .N-ob c .N-ob d) ((η⁻¹ .trans .N-ob c .N-ob d) (lift f))))
                  ≡⟨ (λ i → (lower ((η .trans .N-ob c .N-ob d) ((η⁻¹ .trans .N-ob c .N-ob d) (lift (p (~ i))))))) ⟩
                (lower ((η .trans .N-ob c .N-ob d) ((η⁻¹ .trans .N-ob c .N-ob d) (lift ((f ⋆⟨ D ⟩ D .id) ⋆⟨ D ⟩ (G ⟪ C .id ⟫))))))
                  ≡⟨ (λ i → lower ( (η .trans .N-ob c .N-ob d) (((η⁻¹ .trans .N-ob c .N-hom f) (i)) (lift (D .id))))) ⟩
                (lower ((η .trans .N-ob c .N-ob d) (lift ((R⟅-,c⟆ ⟪ f ⟫) (lower ((η⁻¹ .trans .N-ob c .N-ob (G ⟅ c ⟆)) (lift (D .id))))))))
                  ≡⟨ (λ i →  (lower ((η .trans .N-ob c .N-ob d) (lift (ε⋆f≡ϕ i))))) ⟩
                coindϕ ∎
          }
        }
      )

    open UnivElt
    open isUniversal
    -- | Definition 3 → Definition 2
    ParamUniversalElement→PshFunctorRepresentation : ParamUniversalElement → PshFunctorRepresentation
    ParamUniversalElement→PshFunctorRepresentation U =
      (representing-functor , representing-nat-iso)
      where
      Prof*-o→FunctorR : (C : Category ℓC ℓC') (D : Category ℓD ℓD') (R : C *-[ ℓs ]-o D) → Functor (D ^op) (FUNCTOR C (SET ℓs))
      Prof*-o→FunctorR C D R = curryF C (SET _) ⟅ R ⟆

      -- | For Definition 3 → Definition 2, we need to construct a functor
      representing-functor : Functor C D
      representing-functor .F-ob c = fst (fst (U c))
      representing-functor .F-hom {x} {y} ϕ =
        (UniversalElement→UnivElt D (R ∘F (Id {C = D ^op} ,F Constant (D ^op) C y)) (U y))
          .universal .coinduction
          ((((Prof*-o→FunctorR C D R)  ⟅ (fst (fst (U x))) ⟆) ⟪ ϕ ⟫) (snd (fst (U x))))
      representing-functor .F-id {x} =
        let R⟅-,x⟆ = R ∘F (Id {C = D ^op} ,F Constant (D ^op) C x) in
        let (dₓ , θₓ) = (fst (U x)) in
          (UniversalElement→UnivElt D R⟅-,x⟆ (U x))
              .universal .coinduction
            ((((Prof*-o→FunctorR C D R)  ⟅ dₓ ⟆) ⟪ C .id ⟫) θₓ)
          -- Use the fact that curryF is a functor to simplify coinduction target (F-id)
          ≡⟨ (λ i →
              (UniversalElement→UnivElt D R⟅-,x⟆ (U x))
                .universal .coinduction
                ((((Prof*-o→FunctorR C D R)  ⟅ dₓ ⟆) .F-id (i)) θₓ)) ⟩
          (UniversalElement→UnivElt D R⟅-,x⟆ (U x)) .universal .coinduction θₓ
          -- use uniqueness of universal element.
          ≡⟨ sym ((UniversalElement→UnivElt D R⟅-,x⟆ (U x)) .universal .is-uniq θₓ (D .id)
                -- Nested proof that identity also works.
                ( (R⟅-,x⟆ ⟪ D .id ⟫) ((UniversalElement→UnivElt D R⟅-,x⟆ (U x)) .element)
                  ≡⟨ (λ i → (R⟅-,x⟆ .F-id (i)) ((UniversalElement→UnivElt D R⟅-,x⟆ (U x)) .element)) ⟩
                θₓ ∎
                )
          )⟩
        D .id ∎
      representing-functor .F-seq {x} {y} {z} ϕ ψ =
        let Gϕ⋆ψ = representing-functor .F-hom (ϕ ⋆⟨ C ⟩ ψ) in
        let Gϕ = representing-functor .F-hom ϕ in
        let Gψ = representing-functor .F-hom ψ in
        let (dx , εx) = (fst (U x)) in
        let (dy , εy) = (fst (U y)) in
        let (dz , εz) = (fst (U z)) in
        let R⟅-,y⟆ = R ∘F (Id {C = D ^op} ,F Constant (D ^op) C y) in
        let R⟅-,z⟆ = R ∘F (Id {C = D ^op} ,F Constant (D ^op) C z) in
        let R⟅dx,-⟆ = ((Prof*-o→FunctorR C D R) ⟅ dx ⟆) in
        let R⟅dy,-⟆ = ((Prof*-o→FunctorR C D R) ⟅ dy ⟆) in
          ( Gϕ⋆ψ )
          ≡⟨ (λ i → (UniversalElement→UnivElt D R⟅-,z⟆ (U z))
            .universal .coinduction
            (((R⟅dx,-⟆ .F-seq ϕ ψ) (i)) εx)
          ) ⟩
          ((UniversalElement→UnivElt D R⟅-,z⟆ (U z))
            .universal .coinduction
            ((R⟅dx,-⟆ ⟪ ψ ⟫)
              ((R⟅dx,-⟆ ⟪ ϕ ⟫) εx)
            )
          )
          ≡⟨ sym ((UniversalElement→UnivElt D R⟅-,z⟆ (U z)) .universal .is-uniq
            ((R⟅dx,-⟆ ⟪ ψ ⟫)((R⟅dx,-⟆ ⟪ ϕ ⟫) εx))
            -- enough to show that this function also yields above result
            (Gϕ ⋆⟨ D ⟩ Gψ)
            (
              (D [ εz ∘ᴾ⟨ R⟅-,z⟆ ⟩ (Gϕ ⋆⟨ D ⟩ Gψ) ])
                ≡⟨ (λ i → ((R⟅-,z⟆ .F-seq Gψ Gϕ) (i)) εz) ⟩
              (D [ (D [ εz ∘ᴾ⟨ R⟅-,z⟆ ⟩ (Gψ) ]) ∘ᴾ⟨ R⟅-,z⟆ ⟩ Gϕ ])
                ≡⟨ (λ i →
                  (D [
                    (((UniversalElement→UnivElt D R⟅-,z⟆ (U z)) .universal .commutes ((R⟅dy,-⟆ ⟪ ψ ⟫) εy)) (i))
                    ∘ᴾ⟨ R⟅-,z⟆ ⟩ Gϕ ]
                  )
                ) ⟩
              (D [ ((R⟅dy,-⟆ ⟪ ψ ⟫) εy) ∘ᴾ⟨ R⟅-,z⟆ ⟩ Gϕ ])
                ≡⟨ refl ⟩
              ((R ⟪ Gϕ , C .id ⟫) ((R ⟪ D .id , ψ ⟫) (εy)))
                ≡⟨ (λ i → (
                  ((BinMorphDecompR {C = (D ^op)} {D = C} {E = (SET _)}
                    (Gϕ , ψ) R) (~ i)
                  ) (εy)
                )) ⟩
              ((R ⟪ Gϕ , ψ ⟫) (εy))
                ≡⟨ (λ i → (
                  ((BinMorphDecompL {C = (D ^op)} {D = C} {E = (SET _)}
                    (Gϕ , ψ) R) (i)
                  ) (εy)
                )) ⟩
              ((R ⟪ D .id , ψ ⟫) ((R ⟪ Gϕ , C .id ⟫) (εy)))
                ≡⟨ refl ⟩
              ((R⟅dx,-⟆ ⟪ ψ ⟫) (D [ εy ∘ᴾ⟨ R⟅-,y⟆ ⟩ Gϕ ]))
                ≡⟨ (λ i →
                  ((R⟅dx,-⟆ ⟪ ψ ⟫)
                    (((UniversalElement→UnivElt D R⟅-,y⟆ (U y)) .universal .commutes ((R⟅dx,-⟆ ⟪ ϕ ⟫) εx)) (i))
                  )
                ) ⟩
              ((R⟅dx,-⟆ ⟪ ψ ⟫)((R⟅dx,-⟆ ⟪ ϕ ⟫) εx))
            ∎)
          )⟩
          (Gϕ ⋆⟨ D ⟩ Gψ) ∎

      HomFunctor≡Functor→Prof*-o→Functor : (c : C .ob) →
        D [-, representing-functor .F-ob c ]
        ≡
        (Prof*-o→Functor C D (Functor→Prof*-o C D representing-functor) .F-ob c)
      HomFunctor≡Functor→Prof*-o→Functor c = 
        Functor≡
          (λ d → refl)
          (λ f → funExt (λ g →
            f ⋆⟨ D ⟩ g
              ≡⟨ solveCat! D ⟩
            HomFunctor D .F-hom (f , D .id) g
              ≡⟨ ((λ i → (HomFunctor D .F-hom (f , representing-functor .F-id (~ i))) g)) ⟩
            (Prof*-o→Functor C D (Functor→Prof*-o C D representing-functor) .F-ob c) .F-hom f g ∎
          ))

      representing-nat-iso  : NatIso
          (Prof*-o→Functor C D (LiftF {ℓs}{ℓD'} ∘F R))
          (Prof*-o→Functor C D (LiftF {ℓD'}{ℓs} ∘F (Functor→Prof*-o C D representing-functor)))
      representing-nat-iso  .trans .N-ob c .N-ob d =
        let R⟅-,c⟆ = R ∘F (Id {C = D ^op} ,F Constant (D ^op) C c) in
        (λ f → lift (UniversalElement→UnivElt D R⟅-,c⟆ (U c) .universal .coinduction {b = d} (lower f)))
      representing-nat-iso .trans .N-ob c .N-hom {d}{d'} ϕ =
        let R⟅-,c⟆ = R ∘F (Id {C = D ^op} ,F Constant (D ^op) C c) in
        let εc = U c .fst .snd in
        let coind = UniversalElement→UnivElt D R⟅-,c⟆ (U c) .universal .coinduction in
        funExt λ x → 
          lift (U c .snd (d' , lower ((Prof*-o→Functor C D (funcComp LiftF R) .F-ob c .F-hom ϕ)(x)) ) .fst .fst)
           ≡⟨ (λ i → lift(((coinduction-natural (UniversalElement→UnivElt D R⟅-,c⟆ (U c) .universal) (lower x) ϕ)) (~ i))) ⟩
          lift (D [ coind (lower x) ∘ᴾ⟨ D [-, representing-functor .F-ob c ] ⟩ ϕ ])
          ≡⟨ ((λ i → lift (((HomFunctor≡Functor→Prof*-o→Functor c) i .F-hom ϕ ) (coind (lower x))))  ) ⟩
          lift ((Prof*-o→Functor C D (Functor→Prof*-o C D representing-functor) .F-ob c .F-hom ϕ) (coind (lower x)))∎
      representing-nat-iso .trans .N-hom ψ = {!!}
      representing-nat-iso .nIso c .inv .N-ob d = 
        let εc = U c .fst .snd in
        let R⟅-,c⟆ = R ∘F (Id {C = D ^op} ,F Constant (D ^op) C c) in
        λ f → lift (D [ εc ∘ᴾ⟨ R⟅-,c⟆ ⟩ (lower f) ]) 
      representing-nat-iso .nIso c .inv .N-hom ϕ = {!!}
      representing-nat-iso .nIso c .sec = {!!}
      representing-nat-iso .nIso c .ret = {!!}

    -- | Definition 3 → Definition 4
    ParamUniversalElement→ParamUnivElt : ParamUniversalElement → ParamUnivElt
    ParamUniversalElement→ParamUnivElt U c = UniversalElement→UnivElt D (R ∘F (Id {C = D ^op} ,F Constant (D ^op) C c)) (U c)

    -- | Definition 4 → Definition 3
    ParamUnivElt→ParamUniversalElement : ParamUnivElt → ParamUniversalElement
    ParamUnivElt→ParamUniversalElement U c = UnivElt→UniversalElement D (R ∘F (Id {C = D ^op} ,F Constant (D ^op) C c)) (U c)
