{-# OPTIONS --safe #-}
module Cubical.Categories.Profunctor.AsBifunctor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function renaming (_∘_ to _∘f_)

open import Cubical.Categories.Category hiding (isIso)
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
  -- A definition of profunctor homomorphism that avoids Lifts

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
  ProfIso→NatIso : ProfIso → NatIso (LiftF {ℓR}{ℓmaxCDSR} ∘F (Bifunctor→Functor R)) (LiftF {ℓS}{ℓmaxCDSR} ∘F Bifunctor→Functor S)
  ProfIso→NatIso the-prof-iso =
    binaryNatIso {C = C ^op} {D = D} {E = SET _}
      (funcComp LiftF (Bifunctor→Functor R))
      (funcComp LiftF (Bifunctor→Functor S))
      (λ c → CFixed c)
      (λ d → DFixed d)
      (λ (c , d) → refl)
      where
      CFixed : (c : C .ob)
        → NatIso
          ((curryF D (SET (ℓ-max ℓR ℓmaxCDSR)) ⟅
             funcComp LiftF (Bifunctor→Functor R) ⟆)
               ⟅ c ⟆)
          ((curryF D (SET (ℓ-max ℓR ℓmaxCDSR)) ⟅
             funcComp LiftF (Bifunctor→Functor S) ⟆)
               ⟅ c ⟆)
      CFixed c .trans .N-ob d x = lift (PH-ob (the-prof-iso .fst) (lower x))
      CFixed c .trans .N-hom {d₁}{d₂} ϕ =
        funExt (λ x →
          (CFixed c .trans .N-ob d₂) (lift (Bifunctor.Bif-homR R c ϕ ((R ⟪ (C ^op) .id ⟫l) (x .lower))))
            ≡⟨ ( (λ i → ((CFixed c .trans .N-ob d₂) (lift (R .Bif-homR c ϕ ((R .Bif-idL i) (x .lower))))) ) ) ⟩
          (CFixed c .trans .N-ob d₂) (lift (Bifunctor.Bif-homR R c ϕ ((x .lower))))
            ≡⟨ ((λ i → lift (the-prof-iso .fst .PH-natR (lower x) ϕ i))) ⟩
          lift (Bifunctor.Bif-homR S c ϕ ((PH-ob (the-prof-iso .fst) (lower x))))
            ≡⟨ ((λ i → (lift (Bifunctor.Bif-homR S c ϕ ((S .Bif-idL (~ i)) (PH-ob (the-prof-iso .fst) (lower x))))))) ⟩
          lift (Bifunctor.Bif-homR S c ϕ ((S ⟪ (C ^op) .id ⟫l) (PH-ob (the-prof-iso .fst) (lower x)))) ∎
        )
      CFixed c .nIso =
        λ d →
          isiso
          (λ x → lift (the-prof-iso .snd c d .fst (lower x)))
          (funExt (λ x i → lift (the-prof-iso .snd c d .snd .fst (lower x) i)))
          (funExt (λ x i → lift (the-prof-iso .snd c d .snd .snd (lower x) i)))

      DFixed : (d : D .ob)
        → NatIso ((curryFl (C ^op) (SET (ℓ-max ℓR ℓmaxCDSR)) ⟅
                 funcComp LiftF (Bifunctor→Functor R) ⟆)
                   ⟅ d ⟆)
                 ((curryFl (C ^op) (SET (ℓ-max ℓR ℓmaxCDSR)) ⟅
                   funcComp LiftF (Bifunctor→Functor S) ⟆)
                   ⟅ d ⟆)
      DFixed d .trans .N-ob c x = lift (PH-ob (the-prof-iso .fst) (lower x))
      DFixed d .trans .N-hom {c₁}{c₂} ψ =
        funExt (λ x → 
          (DFixed d .trans .N-ob c₂) (lift (Bif-homR R c₂ (id D) ((R ⟪ ψ ⟫l) (lower x))))
            ≡⟨ (λ i →  (DFixed d .trans .N-ob c₂) (lift (R .Bif-idR i ((R ⟪ ψ ⟫l) (lower x))))) ⟩
          (DFixed d .trans .N-ob c₂) ((lift ((R ⟪ ψ ⟫l) (lower x))))
            ≡⟨ (λ i → lift (the-prof-iso .fst .PH-natL ψ (lower x) i)) ⟩
          lift ((S ⟪ ψ ⟫l) ((DFixed d .trans) .N-ob c₁ x .lower))
            ≡⟨ ((λ i → lift ((S .Bif-idR (~ i)) ((S ⟪ ψ ⟫l) (DFixed d .trans .N-ob c₁ x .lower)))) ) ⟩
          lift (F-hom (Bifunctor→Functor S) (ψ , id D) (PH-ob (the-prof-iso .fst) (lower x))) ∎
        )
      DFixed d .nIso =
        λ c →
          isiso
          (λ x → lift (the-prof-iso .snd c d .fst (lower x)))
          (funExt (λ x i → lift (the-prof-iso .snd c d .snd .fst (lower x) i)))
          (funExt (λ x i → lift (the-prof-iso .snd c d .snd .snd (lower x) i)))

  NatIso→ProfIso : NatIso (LiftF {ℓR}{ℓmaxCDSR} ∘F (Bifunctor→Functor R)) (LiftF {ℓS}{ℓmaxCDSR} ∘F Bifunctor→Functor S)
                   → ProfIso
  NatIso→ProfIso η =
    (record {
      PH-ob = λ {c d} r → lower (η .trans .N-ob (c , d) (lift r)) ;
      PH-natL = λ {c c' d} f r → 
        lower (η .trans .N-ob (c , d) (lift ((R ⟪ f ⟫l) r)))
          ≡⟨ (λ i → lower (η .trans .N-ob (c , d) (lift ((R .Bif-idR (~ i)) ((R ⟪ f ⟫l )r))))) ⟩
        lower ((N-ob (η .trans) (c , d) ∘f ((LiftF {ℓR}{ℓmaxCDSR} ∘F Bifunctor→Functor R) ⟪ f , D .id ⟫)) (lift r))
          ≡⟨ ((λ i → lower (η .trans .N-hom {x = (c' , d)} {y = (c , d)} (f , D .id) i (lift r)))) ⟩
        lower ((((LiftF {ℓS}{ℓmaxCDSR} ∘F Bifunctor→Functor S) ⟪ f , D .id ⟫) ∘f (N-ob (η .trans) (c' , d))) (lift r))
          ≡⟨ (λ i → S .Bif-idR i ((S ⟪ f ⟫l) (lower (η .trans .N-ob (c' , d) (lift r))))) ⟩
        (S ⟪ f ⟫l) (lower (η .trans .N-ob (c' , d) (lift r))) ∎
     ;
        -- lower (η .trans .N-hom {x = (c' , d)} {y = (c , d)} (f , D .id) {!i!} (lift r));
      PH-natR = λ {d d' c} r g → 
        lower (η .trans .N-ob (d , c) (lift ((R ⟪ g ⟫r) r)))
         ≡⟨ (λ i → lower (η .trans .N-ob (d , c) (lift ((R .Bif-idL (~ i)) (( R ⟪ g ⟫r ) r) )))) ⟩
        {!!}
         ≡⟨ {!!} ⟩
        (S ⟪ g ⟫r) (lower (η .trans .N-ob (d , d') (lift r))) ∎
    }) ,
    (λ c d → {!!})

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

  ProfRepresentation→PshFunctorRepresentation : ProfRepresentation → PshFunctorRepresentation
  ProfRepresentation→PshFunctorRepresentation (G , η) =
    G , preservesNatIsosF (curryFl (D ^op) (SET _)) {!ProfIso→NatIso!}
    -- (G ,
    -- (preservesNatIsosF (curryFl (D ^op) (SET _)) η)
    -- )

  PshFunctorRepresentation→ProfRepresentation : PshFunctorRepresentation → ProfRepresentation
  PshFunctorRepresentation→ProfRepresentation (G , η) = {!!} , {!!}

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
