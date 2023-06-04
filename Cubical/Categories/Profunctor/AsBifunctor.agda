{-# OPTIONS --safe #-}
module Cubical.Categories.Profunctor.AsBifunctor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function renaming (_∘_ to _∘f_)

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor
open import Cubical.Categories.Bifunctor.Base
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.BinProduct.More
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Functors.More
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Data.Sigma

open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Instances.Functors.More

private
  variable
    ℓC ℓC' ℓD ℓD' ℓS ℓR : Level

open Category
open Functor
open UnivElt
open isUniversal
open Bifunctor

--TODO put this somewhere better
_⋆f_ : {ℓ : Level} {A : Type ℓ } → {B : A → Type ℓ} → {C : (a : A) → B a → Type ℓ} →
       (f : (a : A) → B a) → (g : {a : A} → (b : B a) → C a b) → (a : A) → C a (f a)
f ⋆f g = λ x → (g ∘f f) x

_o-[_]-*_ : (C : Category ℓC ℓC') → ∀ ℓS → (D : Category ℓD ℓD') → Type _
C o-[ ℓS ]-* D = Bifunctor (C ^op) D (SET ℓS)

_*-[_]-o_ : (C : Category ℓC ℓC') → ∀ ℓS → (D : Category ℓD ℓD') → Type _
C *-[ ℓS ]-o D = D o-[ ℓS ]-* C

module _  {C : Category ℓC ℓC'}{D : Category ℓD ℓD'} {ℓS : Level} where
  -- Product of a presheaf with a profunctor
  -- This could be done by turning the presheaf into a profunctor
  -- first but at the cost of extra ids.
  _o×_ : (P : 𝓟o C ℓS) → (R : C o-[ ℓS ]-* D) → C o-[ ℓS ]-* D
  (P o× R) .Bif-ob c d = ⟨ P ⟅ c ⟆ ⟩ × ⟨ R ⟅ c , d ⟆b ⟩ , isSet× ((P ⟅ c ⟆) .snd) ((R ⟅ c , d ⟆b) .snd) -- should be a combinator somewhere
  (P o× R) .Bif-homL f d (p , r) = (P ⟪ f ⟫) p , (R ⟪ f ⟫l) r
  (P o× R) .Bif-homR c g (p , r) = p , ((R ⟪ g ⟫r) r)
  (P o× R) .Bif-idL = funExt λ (p , r) → λ i → (P .F-id i p , R .Bif-idL i r)
  (P o× R) .Bif-idR = funExt λ (p , r) → λ i → (p , R .Bif-idR i r)
  (P o× R) .Bif-seqL f f' = funExt (λ (p , r) i → (P .F-seq f f' i p , R .Bif-seqL f f' i r))
  (P o× R) .Bif-seqR g g' = funExt (λ (p , r) i → (p , R .Bif-seqR g g' i r))
  (P o× R) .Bif-assoc f g = funExt λ (p , r) i → ((P ⟪ f ⟫) p) , (R .Bif-assoc f g i r)

module _  {C : Category ℓC ℓC'}{D : Category ℓD ℓD'} (R : C o-[ ℓR ]-* D) (S : C o-[ ℓS ]-* D) where
  -- A definition of profunctor homomorphism that avoids Lfts

  ℓmaxCDSR : Level
  ℓmaxCDSR = (ℓ-max ℓC (ℓ-max ℓC' (ℓ-max ℓD (ℓ-max ℓD' (ℓ-max ℓS ℓR)))))

  open NatIso
  open Functor
  open Category
  open NatTrans
  open Bifunctor

  record ProfHomo : Type ℓmaxCDSR where
    field
      PH-ob : ∀ {c d} → (r : ⟨ R ⟅ c , d ⟆b ⟩) → ⟨ S ⟅ c , d ⟆b ⟩
      PH-natL : ∀ {c c' d} (f : C [ c , c' ]) (r : ⟨ R ⟅ c' , d ⟆b ⟩)
              → PH-ob ((R ⟪ f ⟫l) r) ≡ (S ⟪ f ⟫l) (PH-ob r)
      PH-natR : ∀ {c d d'} (r : ⟨ R ⟅ c , d ⟆b ⟩) (g : D [ d , d' ])
              → PH-ob ((R ⟪ g ⟫r) r) ≡ (S ⟪ g ⟫r) (PH-ob r)

  open ProfHomo
  ProfIso : Type _
  ProfIso = Σ[ ϕ ∈ ProfHomo ] ∀ c d → isIso (ϕ .PH-ob {c}{d})

  -- Repackage the profunctor isomorphism as a natural isomorphism between functors
  -- ProfIso→NatIso : ProfIso → NatIso (LiftF {ℓR}{ℓmaxCDSR} ∘F (Bifunctor→Functor R)) (LiftF {ℓS}{ℓmaxCDSR} ∘F Bifunctor→Functor S)
  -- ProfIso→NatIso the-prof-iso =
  --   binaryNatIso {C = C ^op} {D = D} {E = SET _}
  --     (funcComp LiftF (Bifunctor→Functor R))
  --     (funcComp LiftF (Bifunctor→Functor S))
  --     (λ c → CFixed c)
  --     (λ d → DFixed d)
  --     (λ (c , d) → refl)
  --     where
  --     CFixed : (c : C .ob)
  --       → NatIso
  --         ((curryF D (SET (ℓ-max ℓR ℓmaxCDSR)) ⟅
  --            funcComp LiftF (Bifunctor→Functor R) ⟆)
  --              ⟅ c ⟆)
  --         ((curryF D (SET (ℓ-max ℓR ℓmaxCDSR)) ⟅
  --            funcComp LiftF (Bifunctor→Functor S) ⟆)
  --              ⟅ c ⟆)
  --     CFixed c .trans .N-ob d x = lift (PH-ob (the-prof-iso .fst) (lower x))
  --     CFixed c .trans .N-hom {d₁}{d₂} ϕ =
  --       funExt (λ x →
  --         (CFixed c .trans .N-ob d₂) (lift (Bifunctor.Bif-homR R c ϕ ((R ⟪ (C ^op) .id ⟫l) (x .lower))))
  --           ≡⟨ ( (λ i → ((CFixed c .trans .N-ob d₂) (lift (R .Bif-homR c ϕ ((R .Bif-idL i) (x .lower))))) ) ) ⟩
  --         (CFixed c .trans .N-ob d₂) (lift (Bifunctor.Bif-homR R c ϕ ((x .lower))))
  --           ≡⟨ ((λ i → lift (the-prof-iso .fst .PH-natR (lower x) ϕ i))) ⟩
  --         lift (Bifunctor.Bif-homR S c ϕ ((PH-ob (the-prof-iso .fst) (lower x))))
  --           ≡⟨ ((λ i → (lift (Bifunctor.Bif-homR S c ϕ ((S .Bif-idL (~ i)) (PH-ob (the-prof-iso .fst) (lower x))))))) ⟩
  --         lift (Bifunctor.Bif-homR S c ϕ ((S ⟪ (C ^op) .id ⟫l) (PH-ob (the-prof-iso .fst) (lower x)))) ∎
  --       )
  --     CFixed c .nIso =
  --       λ d →
  --         isiso
  --         (λ x → lift (the-prof-iso .snd c d .fst (lower x)))
  --         (funExt (λ x i → lift (the-prof-iso .snd c d .snd .fst (lower x) i)))
  --         (funExt (λ x i → lift (the-prof-iso .snd c d .snd .snd (lower x) i)))

  --     DFixed : (d : D .ob)
  --       → NatIso ((curryFl (C ^op) (SET (ℓ-max ℓR ℓmaxCDSR)) ⟅
  --                funcComp LiftF (Bifunctor→Functor R) ⟆)
  --                  ⟅ d ⟆)
  --                ((curryFl (C ^op) (SET (ℓ-max ℓR ℓmaxCDSR)) ⟅
  --                  funcComp LiftF (Bifunctor→Functor S) ⟆)
  --                  ⟅ d ⟆)
  --     DFixed d .trans .N-ob c x = lift (PH-ob (the-prof-iso .fst) (lower x))
  --     DFixed d .trans .N-hom {c₁}{c₂} ψ =
  --       funExt (λ x →
  --         (DFixed d .trans .N-ob c₂) (lift (Bif-homR R c₂ (id D) ((R ⟪ ψ ⟫l) (lower x))))
  --           ≡⟨ (λ i →  (DFixed d .trans .N-ob c₂) (lift (R .Bif-idR i ((R ⟪ ψ ⟫l) (lower x))))) ⟩
  --         (DFixed d .trans .N-ob c₂) ((lift ((R ⟪ ψ ⟫l) (lower x))))
  --           ≡⟨ (λ i → lift (the-prof-iso .fst .PH-natL ψ (lower x) i)) ⟩
  --         lift ((S ⟪ ψ ⟫l) ((DFixed d .trans) .N-ob c₁ x .lower))
  --           ≡⟨ ((λ i → lift ((S .Bif-idR (~ i)) ((S ⟪ ψ ⟫l) (DFixed d .trans .N-ob c₁ x .lower)))) ) ⟩
  --         lift (F-hom (Bifunctor→Functor S) (ψ , id D) (PH-ob (the-prof-iso .fst) (lower x))) ∎
  --       )
  --     DFixed d .nIso =
  --       λ c →
  --         isiso
  --         (λ x → lift (the-prof-iso .snd c d .fst (lower x)))
  --         (funExt (λ x i → lift (the-prof-iso .snd c d .snd .fst (lower x) i)))
  --         (funExt (λ x i → lift (the-prof-iso .snd c d .snd .snd (lower x) i)))

  -- NatIso→ProfIso : NatIso (LiftF {ℓR}{ℓmaxCDSR} ∘F (Bifunctor→Functor R)) (LiftF {ℓS}{ℓmaxCDSR} ∘F Bifunctor→Functor S)
  --                  → ProfIso
  -- NatIso→ProfIso η =
  --   (record {
  --     PH-ob = λ {c d} r → lower (η .trans .N-ob (c , d) (lift r)) ;
  --     PH-natL = λ {c c' d} f r →
  --       lower (η .trans .N-ob (c , d) (lift ((R ⟪ f ⟫l) r)))
  --         ≡⟨ (λ i → lower (η .trans .N-ob (c , d) (lift ((R .Bif-idR (~ i)) ((R ⟪ f ⟫l )r))))) ⟩
  --       lower ((N-ob (η .trans) (c , d) ∘f ((LiftF {ℓR}{ℓmaxCDSR} ∘F Bifunctor→Functor R) ⟪ f , D .id ⟫)) (lift r))
  --         ≡⟨ ((λ i → lower (η .trans .N-hom {x = (c' , d)} {y = (c , d)} (f , D .id) i (lift r)))) ⟩
  --       lower ((((LiftF {ℓS}{ℓmaxCDSR} ∘F Bifunctor→Functor S) ⟪ f , D .id ⟫) ∘f (N-ob (η .trans) (c' , d))) (lift r))
  --         ≡⟨ (λ i → S .Bif-idR i ((S ⟪ f ⟫l) (lower (η .trans .N-ob (c' , d) (lift r))))) ⟩
  --       (S ⟪ f ⟫l) (lower (η .trans .N-ob (c' , d) (lift r))) ∎
  --    ;
  --       -- lower (η .trans .N-hom {x = (c' , d)} {y = (c , d)} (f , D .id) {!i!} (lift r));
  --     PH-natR = λ {d d' c} r g →
  --       lower (η .trans .N-ob (d , c) (lift ((R ⟪ g ⟫r) r)))
  --        ≡⟨ (λ i → lower (η .trans .N-ob (d , c) (lift ((R .Bif-idL (~ i)) (( R ⟪ g ⟫r ) r) )))) ⟩
  --       {!!}
  --        ≡⟨ {!!} ⟩
  --       (S ⟪ g ⟫r) (lower (η .trans .N-ob (d , d') (lift r))) ∎
  --   }) ,
    -- (λ c d → {!!})

open ProfHomo

Functor→Prof*-o : (C : Category ℓC ℓC') (D : Category ℓD ℓD') (F : Functor C D) → C *-[ ℓD' ]-o D
Functor→Prof*-o C D F = HomBif D ∘Fr F

Functor→Profo-* : (C : Category ℓC ℓC') (D : Category ℓD ℓD') (F : Functor C D) → C o-[ ℓD' ]-* D
Functor→Profo-* C D F = HomBif D ∘Fl (F ^opF)

Prof*-o→Functor : (C : Category ℓC ℓC') (D : Category ℓD ℓD') (R : C *-[ ℓS ]-o D) → Functor C (FUNCTOR (D ^op) (SET ℓS))
Prof*-o→Functor C D R = curryFl (D ^op) (SET _) ⟅ Bifunctor→Functor R ⟆

Profo-*→Functor : (C : Category ℓC ℓC') (D : Category ℓD ℓD') (R : C o-[ ℓS ]-* D) → Functor (C ^op) (FUNCTOR D (SET ℓS))
Profo-*→Functor C D R = curryF D (SET _) ⟅ Bifunctor→Functor R ⟆

module _ (C : Category ℓC ℓC') (D : Category ℓD ℓD') (R : C *-[ ℓS ]-o D) where

  open NatTrans
  open NatIso
  open isIsoC

  ProfRepresents : Functor C D → Type _
  ProfRepresents G = ProfIso {C = D}{D = C} R (Functor→Prof*-o C D G)

  ProfRepresentation : Type _
  ProfRepresentation = Σ[ G ∈ Functor C D ] ProfRepresents G

  PshFunctorRepresentation : Type _
  PshFunctorRepresentation =
    Σ[ G ∈ Functor C D ]
    NatIso (Prof*-o→Functor C D ((LiftF {ℓS}{ℓD'}) ∘Fb R ))
           (Prof*-o→Functor C D (LiftF {ℓD'}{ℓS} ∘Fb (Functor→Prof*-o C D G)))


  RepresentableAt : (c : C .ob) → Type _
  RepresentableAt c = UnivElt D (pAppR R c)

  ParamUnivElt : Type _
  ParamUnivElt = (c : C .ob) → RepresentableAt c

  ParamUniversalElement : Type _
  ParamUniversalElement = (c : C .ob) → UniversalElement D (pAppR R c)

  -- Profunctor Representation → Presheaf Representation
  ProfRepresentation→PshFunctorRepresentation : ProfRepresentation → PshFunctorRepresentation
  ProfRepresentation→PshFunctorRepresentation (G , η) =
    G ,
    record {
      trans = the-trans ;
      nIso = λ c →
        FUNCTORIso
          (D ^op)
          (SET (ℓ-max ℓD' ℓS))
          (the-trans .N-ob c)
          λ d →
            isiso
              (λ x → lift ((η .snd d c .fst) (lower x)))
              (λ i x → lift ((η .snd d c .snd .fst) (lower x) i))
              (λ i x → lift ((η .snd d c .snd .snd) (lower x) i))
      }
      where
      the-trans : NatTrans (Prof*-o→Functor C D (bifCompF LiftF R)) (Prof*-o→Functor C D (bifCompF LiftF (Functor→Prof*-o C D G)))
      the-trans .N-ob c =
        natTrans
          (λ d x → lift (η .fst .PH-ob (lower x)))
          (λ f → funExt (λ x →
            (Prof*-o→Functor C D (bifCompF LiftF R) .F-ob c .F-hom f
              ⋆f
              (λ x₂ → lift (η .fst .PH-ob (lower x₂)))) x
              ≡⟨ (λ i → lift (η .fst .PH-ob (((R ⟪ f ⟫l) ⋆f R .Bif-idR i) (lower x)))) ⟩
            lift (PH-ob (η .fst) ((R ⟪ f ⟫l) (lower x)))
              ≡⟨ (λ i → lift (η .fst .PH-natL f (lower x) i)) ⟩
            lift ((Functor→Prof*-o C D G ⟪ f ⟫l) (PH-ob (η .fst) (lower x)))
              ≡⟨ (λ i → lift (((Functor→Prof*-o C D G) ⟪ f ⟫l ⋆f Functor→Prof*-o C D G .Bif-idR (~ i)) (η .fst .PH-ob (lower x)))) ⟩
            ((λ x₂ → lift (η .fst .PH-ob (lower x₂)))
              ⋆f
              Prof*-o→Functor C D (bifCompF LiftF (Functor→Prof*-o C D G)) .F-ob c .F-hom f) x ∎
             ))
      the-trans .N-hom f =
        makeNatTransPath
              (funExt (λ d → funExt λ x →
                lift (η .fst .PH-ob ((Bif-homL R (id D) _ ⋆f (R ⟪ f ⟫r)) (lower x)))
                  ≡⟨ (λ i → lift (η .fst .PH-ob ((R .Bif-idL i ⋆f (R ⟪ f ⟫r)) (lower x)))) ⟩
                lift (PH-ob (η .fst) ((R ⟪ f ⟫r) (lower x)))
                  ≡⟨ (λ i → lift (η .fst .PH-natR (lower x) f i)) ⟩
                lift ((Functor→Prof*-o C D G ⟪ f ⟫r) (PH-ob (η .fst) (lower x)))
                  ≡⟨ ((λ i → lift ((Functor→Prof*-o C D G .Bif-idL (~ i) ⋆f (Functor→Prof*-o C D G ⟪ f ⟫r )) (η .fst .PH-ob (lower x))))) ⟩
                lift
                  ((Bif-homL (Functor→Prof*-o C D G) (id D) _ ⋆f
                    (Functor→Prof*-o C D G ⟪ f ⟫r))
                   (η .fst .PH-ob (lower x))) ∎))

  -- Presheaf Representation → Profunctor Representation
  PshFunctorRepresentation→ProfRepresentation : PshFunctorRepresentation → ProfRepresentation
  PshFunctorRepresentation→ProfRepresentation (G , η) =
    G ,
    (record {
      PH-ob = λ {d}{c} r → lower ((η .trans .N-ob c .N-ob d) (lift r)) ;
      PH-natL = λ {d}{d'}{c} f r → 
        lower (((η .trans .N-ob c .N-ob d) ∘f ((bifCompF LiftF R) .Bif-homL f c)) (lift r))
         ≡⟨ ((λ i → lower (((η .trans .N-ob c .N-ob d) ∘f ( (bifCompF LiftF R) .Bif-homL f c ⋆f (bifCompF LiftF R) .Bif-idR (~ i))) (lift r)))) ⟩
        lower (((η .trans .N-ob c .N-ob d) ∘f (((bifCompF LiftF R) .Bif-homL f c) ⋆f (bifCompF LiftF R) .Bif-homR d (C .id))) (lift r))
         ≡⟨ ((λ i → lower ((η .trans .N-ob c .N-hom f i) (lift r)))) ⟩
        lower ((N-ob (η .trans .N-ob c) d' ⋆f Prof*-o→Functor C D (bifCompF LiftF (Functor→Prof*-o C D G)) .F-ob c .F-hom f) (lift r))
         ≡⟨ ((λ i → ((Functor→Prof*-o C D G ⟪ f ⟫l) ⋆f (Functor→Prof*-o C D G) .Bif-idR i) (lower (η .trans .N-ob c .N-ob d' (lift r))))) ⟩
        (Functor→Prof*-o C D G ⟪ f ⟫l)
          (lower (η .trans .N-ob c .N-ob d' (lift r))) ∎
       ;
      PH-natR = λ {c}{d}{d'} r g → 
        lower (η .trans .N-ob d' .N-ob c (lift ((R ⟪ g ⟫r) r)))
          ≡⟨ (λ i → lower (η .trans .N-ob d' .N-ob c (lift ((R .Bif-idL (~ i) ⋆f R ⟪ g ⟫r) r)))) ⟩
        lower
          ((Prof*-o→Functor C D (bifCompF LiftF R) .F-hom g .N-ob c ⋆f N-ob (η .trans) d' .N-ob c) (lift r))
          ≡⟨ (λ i → lower ((η .trans .N-hom g i .N-ob c) (lift r))) ⟩
        lower ((N-ob (η .trans) d .N-ob c ⋆f Prof*-o→Functor C D (bifCompF LiftF (Functor→Prof*-o C D G)) .F-hom g .N-ob c) (lift r))
          ≡⟨ ((λ i → (Functor→Prof*-o C D G .Bif-idL i ⋆f (Functor→Prof*-o C D G ⟪ g ⟫r)) (lower (η .trans .N-ob d .N-ob c (lift r))))) ⟩
        (Functor→Prof*-o C D G ⟪ g ⟫r)
          (lower (η .trans .N-ob d .N-ob c (lift r))) ∎
      }) ,
    λ d c →
      (λ x → lower (η .nIso c .inv .N-ob d (lift x))) ,
      (λ x i → lower ((η .nIso c .sec i .N-ob d) (lift x))) ,
      (λ x i → lower((η .nIso c .ret i .N-ob d) (lift x)))


  open NatIso
  open NatTrans
  open isIsoC

  -- Psh → UnivElt
  PshFunctorRepresentation→ParamUnivElt : PshFunctorRepresentation → ParamUnivElt
  PshFunctorRepresentation→ParamUnivElt (G , η) = (λ c →
    let R⟅-,c⟆ = (pAppR R c) in
    let η⁻¹ = symNatIso η in
      record {
        vertex = (G ⟅ c ⟆) ;
        element = lower ((η⁻¹ .trans .N-ob c .N-ob (G ⟅ c ⟆)) (lift (D .id))) ;
        universal = record {
          coinduction = λ {d} ϕ → lower ((η .trans .N-ob c .N-ob d) (lift ϕ));
          commutes = (λ {d} ϕ →
            let coindϕ = (lower ((η .trans .N-ob c .N-ob d) (lift ϕ))) in
            lower (((LiftF ∘F R⟅-,c⟆) ⟪ coindϕ ⟫) ((η⁻¹ .trans .N-ob c .N-ob (G ⟅ c ⟆)) (lift (D .id))))
              ≡⟨ (λ i → lower (((LiftF ∘Fb R ) .Bif-idR (~ i)) (((LiftF ∘Fb R ) .Bif-homL coindϕ c) ((η⁻¹ .trans .N-ob c .N-ob (G ⟅ c ⟆)) (lift (D .id)))))) ⟩
            lower ((((Prof*-o→Functor C D ((LiftF {ℓS}{ℓD'}) ∘Fb R )) ⟅ c ⟆) ⟪ coindϕ ⟫) ((η⁻¹ .trans .N-ob c .N-ob (G ⟅ c ⟆)) (lift (D .id))))
              ≡⟨ (λ i → lower ((((η⁻¹ .trans .N-ob c .N-hom coindϕ) (~ i)) (lift (D .id))))) ⟩
            lower ((η⁻¹ .trans .N-ob c .N-ob d) (((Bifunctor→Functor ((LiftF {ℓD'}{ℓS}) ∘Fb (HomBif D))) ⟪ coindϕ , G ⟪ C .id ⟫ ⟫) (lift (D .id))))
              ≡⟨ ( λ i → lower ((η⁻¹ .trans .N-ob c .N-ob d) (((Bifunctor→Functor ((LiftF {ℓD'}{ℓS}) ∘Fb (HomBif D))) ⟪ coindϕ , G .F-id (i) ⟫) (lift (D .id))))) ⟩
            lower ((η⁻¹ .trans .N-ob c .N-ob d) (((Bifunctor→Functor ((LiftF {ℓD'}{ℓS}) ∘Fb (HomBif D))) ⟪ coindϕ , D .id ⟫) (lift (D .id))))
              ≡⟨ (λ i →
                lower ((η⁻¹ .trans .N-ob c .N-ob d) ((((LiftF {ℓD'}{ℓS}) ∘Fb (HomBif D)) .Bif-idR (i))
                  ((((LiftF {ℓD'}{ℓS}) ∘Fb (HomBif D)) .Bif-homL coindϕ (G ⟅ c ⟆)) (lift (D .id))))
                )
                ) ⟩
            lower ((η⁻¹ .trans .N-ob c .N-ob d) (lift (coindϕ ⋆⟨ D ⟩ (D .id))))
              ≡⟨ (λ i → lower ((η⁻¹ .trans .N-ob c .N-ob d) (lift (D .⋆IdR coindϕ (i))))) ⟩
            lower ((η⁻¹ .trans .N-ob c .N-ob d) (lift (coindϕ)))
              ≡⟨ (λ i → lower ((((η .nIso c .ret) (i)) .N-ob d) (lift ϕ))) ⟩
            ϕ ∎) ;
          is-uniq =
            λ {d} ϕ f ε⋆f≡ϕ →
            let coindϕ = (lower ((η .trans .N-ob c .N-ob d) (lift ϕ))) in
              f
                ≡⟨ sym (D .⋆IdR f) ⟩
              (f ⋆⟨ D ⟩ D .id)
                ≡⟨ (λ i → (((HomBif D) .Bif-idR (~ i)) (((HomBif D) .Bif-homL f (G ⟅ c ⟆)) (D .id)))) ⟩
              (((Bifunctor→Functor (HomBif D)) ⟪ f , D .id ⟫) (D .id))
                ≡⟨ (λ i → (((Bifunctor→Functor (HomBif D)) ⟪ f , G .F-id (~ i) ⟫) (D .id))) ⟩
              (((Bifunctor→Functor (HomBif D)) ⟪ f , G ⟪ C .id ⟫ ⟫) (D .id))
                ≡⟨ (λ i → lower(((η .nIso c .sec) (~ i) .N-ob d) (lift (((Bifunctor→Functor (HomBif D)) ⟪ f , G ⟪ C .id ⟫ ⟫) (D .id))))) ⟩
              lower ((η .trans .N-ob c .N-ob d) ((η⁻¹ .trans .N-ob c .N-ob d) (lift (((Bifunctor→Functor (HomBif D)) ⟪ f , G ⟪ C .id ⟫ ⟫) (D .id)))))
                ≡⟨ (λ i → lower ((η .trans .N-ob c .N-ob d) (((η⁻¹ .trans .N-ob c .N-hom f) (i)) (lift (D .id))))) ⟩
              lower ((η .trans .N-ob c .N-ob d) ((((Prof*-o→Functor C D ((LiftF {ℓS}{ℓD'}) ∘Fb R )) ⟅ c ⟆) ⟪ f ⟫) ((η⁻¹ .trans .N-ob c .N-ob (G ⟅ c ⟆)) (lift (D .id)))))
                ≡⟨ ( λ i → lower ((η .trans .N-ob c .N-ob d) (((LiftF ∘Fb R ) .Bif-idR (i)) (((LiftF ∘Fb R ) .Bif-homL f c) ((η⁻¹ .trans .N-ob c .N-ob (G ⟅ c ⟆)) (lift (D .id))))))) ⟩
              lower ((η .trans .N-ob c .N-ob d) (lift ((R⟅-,c⟆ ⟪ f ⟫) (lower ((η⁻¹ .trans .N-ob c .N-ob (G ⟅ c ⟆)) (lift (D .id)))))))
                ≡⟨ (λ i →  (lower ((η .trans .N-ob c .N-ob d) (lift (ε⋆f≡ϕ i))))) ⟩
              coindϕ ∎
        }
      }
    )


  ParamUnivElt→Functor : ParamUnivElt → Functor C D
  ParamUnivElt→Functor ues .F-ob c = ues c .vertex
  ParamUnivElt→Functor ues .F-hom {x = c}{y = c'} f = ues c' .universal .coinduction ((R ⟪ f ⟫r) (ues c .element))
  ParamUnivElt→Functor ues .F-id {x = c} =
    cong (ues c .universal .coinduction) (λ i → R .Bif-idR i (ues c .element))
    ∙ sym (coinduction-elt (ues c .universal))
  ParamUnivElt→Functor ues .F-seq {x = c}{y = c'}{z = c''} f g =
    -- Both sides are ≡ to R .Bif-homR (ues c .vertex) g (R .Bif-homR (ues c .vertex) f (ues c .element))
    cong (ues c'' .universal .coinduction) ((λ i → R .Bif-seqR f g i (ues c .element)))
    ∙ cong (coinduction (ues c'' .universal))
        ( cong (R .Bif-homR (ues c .vertex) g)
          (sym (ues c' .universal .commutes _))
        ∙ (λ i → R .Bif-assoc (ues c' .universal .coinduction ((R ⟪ f ⟫r) (ues c .element))) g i (ues c' .element)))
    ∙ sym (coinduction-natural (ues c'' .universal) _ _)



  -- UnivElt → Psh
  ParamUnivElt→PshFunctorRepresentation : ParamUnivElt → PshFunctorRepresentation
  ParamUnivElt→PshFunctorRepresentation ues = (representing-functor , representing-nat-iso) where
    representing-functor : Functor C D
    representing-functor = ParamUnivElt→Functor ues

    rep-nat-iso-trans : (c : C .ob) →
      NatTrans (Prof*-o→Functor C D (LiftF {ℓS}{ℓD'} ∘Fb R) .F-ob c)
               (Prof*-o→Functor C D (LiftF {ℓD'}{ℓS} ∘Fb (Functor→Prof*-o C D representing-functor)) .F-ob c)
    rep-nat-iso-trans c .N-ob d  =
      let R⟅-,c⟆ = (pAppR R c) in
      (λ f → lift {ℓD'}{ℓS} ((ues c) .universal .coinduction {b = d} (lower {ℓS}{ℓD'} f)))
    rep-nat-iso-trans c .N-hom {d}{d'} ϕ =
      let R⟅-,c⟆ = (pAppR R c) in
      let εc = ues c .element in
      let coind = (ues c) .universal .coinduction in
      funExt λ x →
        lift (coind (((Prof*-o→Functor C D R .F-ob c) ⟪ ϕ ⟫) (lower x)))
          ≡⟨ ( λ i → lift (coind ((R .Bif-idR (i)) ((R .Bif-homL ϕ c) (lower x))))) ⟩
        lift (coind (D [ (lower x) ∘ᴾ⟨ R⟅-,c⟆ ⟩ ϕ ] ))
          ≡⟨ (λ i → lift ((coinduction-natural ((ues c) .universal) (lower x) ϕ) (~ i))) ⟩
        lift ((coind (lower x)) ∘⟨ D ⟩ ϕ )
          ≡⟨ (λ i → lift (((HomBif D) .Bif-idR (~ i)) (((HomBif D) .Bif-homL ϕ _) (coind (lower x)))) ) ⟩
        lift (((Bifunctor→Functor (HomBif D)) ⟪ ϕ , D .id ⟫ ) (coind (lower x)))
          ≡⟨ (λ i → lift (((Bifunctor→Functor (HomBif D)) ⟪ ϕ , representing-functor .F-id (~ i) ⟫ ) (coind (lower x)))) ⟩
        lift (((Bifunctor→Functor (HomBif D)) ⟪ ϕ , representing-functor ⟪ C . id ⟫ ⟫ ) (coind (lower x))) ∎

    representing-nat-iso  : NatIso
        (Prof*-o→Functor C D (LiftF {ℓS}{ℓD'} ∘Fb R))
        (Prof*-o→Functor C D (LiftF {ℓD'}{ℓS} ∘Fb (Functor→Prof*-o C D representing-functor)))
    representing-nat-iso .trans .N-ob c = rep-nat-iso-trans c
    representing-nat-iso .trans .N-hom {x}{y} ψ =
      let R⟅-,x⟆ = (pAppR R x) in
      let R⟅-,y⟆ = (pAppR R y) in
      let εy = ues y .element in
      let εx = ues x .element in
      let coindx = ues x .universal .coinduction in
      let coindy = ues y .universal .coinduction in
      makeNatTransPath (funExt (λ d → funExt (λ α →
          lift (coindy (((Bifunctor→Functor R) ⟪ D .id , ψ ⟫) (lower α)))
            ≡⟨ (λ i → lift (coindy (R .Bif-homR _ ψ ((R .Bif-idL (i)) (lower α))))) ⟩
          lift (coindy (R .Bif-homR _ ψ (lower α)))
            ≡⟨ ( λ i → lift (ues y .universal .is-uniq
                  (R .Bif-homR _ ψ (lower α))
                  ((coindx (lower α)) ⋆⟨ D ⟩ (representing-functor ⟪ ψ ⟫))
                  (
                  (
                    D [ εy ∘ᴾ⟨ R⟅-,y⟆ ⟩ (coindy ((R .Bif-homR _ ψ) εx) ∘⟨ D ⟩ (coindx (lower α))) ]
                      ≡⟨ (λ i → D [ εy ∘ᴾ⟨ R⟅-,y⟆ ⟩ ((coinduction-natural (ues y .universal)
                        ((R .Bif-homR _ ψ) εx) (coindx (lower α))) i)]  ) ⟩
                    D [ εy ∘ᴾ⟨ R⟅-,y⟆ ⟩ coindy ( D [ ((R .Bif-homR _ ψ) εx) ∘ᴾ⟨ R⟅-,y⟆ ⟩ (coindx (lower α)) ]) ]
                      ≡⟨ ues y .universal .commutes (D [ ((R .Bif-homR _ ψ) εx) ∘ᴾ⟨ R⟅-,y⟆ ⟩ (coindx (lower α)) ]) ⟩
                    D [ ((R .Bif-homR _ ψ) εx) ∘ᴾ⟨ R⟅-,y⟆ ⟩ (coindx (lower α)) ]
                     ≡⟨ (λ i → ((R .Bif-assoc (coindx (lower α)) ψ) (~ i)) εx) ⟩
                    (R .Bif-homR _ ψ) (D [ εx ∘ᴾ⟨ R⟅-,x⟆ ⟩ (coindx (lower α)) ])
                     ≡⟨ (λ i → (R .Bif-homR _ ψ) (ues x .universal .commutes (lower α) (i))) ⟩
                    (R .Bif-homR _ ψ (lower α)) ∎
                  )
                  )
                  (~ i))) ⟩
          lift ((coindx (lower α)) ⋆⟨ D ⟩ (representing-functor ⟪ ψ ⟫))
            ≡⟨ (λ i → lift ((HomBif D) .Bif-homR _ (representing-functor ⟪ ψ ⟫) (((HomBif D) .Bif-idL (~ i)) (coindx (lower α))))) ⟩
          lift (((Bifunctor→Functor (HomBif D)) ⟪ D .id , representing-functor ⟪ ψ ⟫ ⟫) (coindx (lower α))) ∎
        
      )))
    representing-nat-iso .nIso c .inv .N-ob d =
      let εc = ues c .element in
      let R⟅-,c⟆ = (pAppR R c) in
      λ f → lift (D [ εc ∘ᴾ⟨ R⟅-,c⟆ ⟩ (lower f) ])
    representing-nat-iso .nIso c .inv .N-hom {d}{d'} ϕ =
      let εc = ues c .element in
      let R⟅-,c⟆ =(pAppR R c) in
      funExt λ x →
        lift (D [ εc ∘ᴾ⟨ R⟅-,c⟆ ⟩ ((Bifunctor→Functor (HomBif D)) ⟪ ϕ , representing-functor ⟪ C .id ⟫ ⟫) (lower x) ])
          ≡⟨ (λ i → lift (D [ εc ∘ᴾ⟨ R⟅-,c⟆ ⟩ ((Bifunctor→Functor (HomBif D)) ⟪ ϕ , representing-functor .F-id i ⟫) (lower x) ])) ⟩
        lift (D [ εc ∘ᴾ⟨ R⟅-,c⟆ ⟩ ((Bifunctor→Functor (HomBif D)) ⟪ ϕ , D .id ⟫ ) (lower x) ])
          ≡⟨ (λ i → lift (D [ εc ∘ᴾ⟨ R⟅-,c⟆ ⟩ ((HomBif D) .Bif-idR (i) (((HomBif D) .Bif-homL ϕ _) (lower x))) ])) ⟩
        lift (D [ εc ∘ᴾ⟨ R⟅-,c⟆ ⟩ (ϕ ⋆⟨ D ⟩ (lower x)) ])
          ≡⟨ (λ i → lift (((R⟅-,c⟆ .F-seq (lower x) ϕ) i) εc)) ⟩
        lift ((R .Bif-homL ϕ _) (D [ εc ∘ᴾ⟨ R⟅-,c⟆ ⟩ (lower x) ]))
          ≡⟨ (λ i → lift ((R .Bif-idR (~ i)) ((R .Bif-homL ϕ _) (D [ εc ∘ᴾ⟨ R⟅-,c⟆ ⟩ (lower x) ])))) ⟩
        lift (((Bifunctor→Functor R) ⟪ ϕ , C .id ⟫) (D [ εc ∘ᴾ⟨ R⟅-,c⟆ ⟩ (lower x) ])) ∎
        
    representing-nat-iso .nIso c .sec =
      let R⟅-,c⟆ = (pAppR R c) in
      makeNatTransPath (funExt λ d → funExt λ x → (λ i → lift ((η-expansion ((ues c) .universal) (lower x)) (~ i))) )
    representing-nat-iso .nIso c .ret =
      let R⟅-,c⟆ = (pAppR R c) in
      makeNatTransPath (funExt λ d → funExt λ x → (λ i → lift (((ues c) .universal .commutes (lower x)) i)))
