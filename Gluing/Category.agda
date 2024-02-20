{-# OPTIONS --safe #-}
module Gluing.Category where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function renaming (_∘_ to _∘f_)

open import Cubical.Data.Quiver.Base as Quiver
open import Cubical.Data.List as List hiding ([_])
open import Cubical.Data.List.Properties as List
open import Cubical.Data.Nat as Nat
open import Cubical.Data.Bool as Bool
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Unit as Unit
open import Cubical.Data.Sigma
open import Cubical.Data.W.Indexed
open import Cubical.Relation.Nullary

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor
open import Cubical.Categories.Bifunctor.Redundant
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.Constructions.Free.Category.Quiver as Free
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section as Disp
open import Cubical.Categories.Displayed.Properties as Disp
open import Cubical.Categories.Displayed.Base.More
open import Cubical.Categories.Displayed.Instances.Sets
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Functors.More
open import Cubical.Categories.Functors.HomFunctor

open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Instances.Functors.More

private
  variable
    ℓB ℓB' ℓC ℓC' ℓD ℓD' ℓS ℓR : Level

-- Consider the free category generated from a graph.

-- This is a very simple sort of language where we have base types and
-- unary function symbols.

data OB : Type ℓ-zero where
  a b c : OB

discreteOB : Discrete OB
discreteOB = sectionDiscrete {A = ℕ}
  (λ { zero → a ; 1 → b ; (suc (suc _)) → c })
  (λ { a → 0 ; b → 1 ; c → 2 })
  (λ { a → refl ; b → refl ; c → refl })
  discreteℕ

isSetOB : isSet OB
isSetOB = Discrete→isSet discreteOB

data MOR : Type ℓ-zero where
  f g h : MOR

discreteMOR : Discrete MOR
discreteMOR = sectionDiscrete {A = ℕ}
  (λ { zero → f ; 1 → g ; (suc (suc _)) → h })
  (λ { f → 0 ; g → 1 ; h → 2 })
  (λ { f → refl ; g → refl ; h → refl })
  discreteℕ

isSetMOR : isSet MOR
isSetMOR = Discrete→isSet discreteMOR

dom cod : MOR → OB
dom f = a
dom g = b
dom h = a

cod f = b
cod g = a
cod h = a

QUIVER : Quiver ℓ-zero ℓ-zero
QUIVER .fst = OB
QUIVER .snd .QuiverOver.mor = MOR
QUIVER .snd .QuiverOver.dom = dom
QUIVER .snd .QuiverOver.cod = cod

FQ = FreeCat QUIVER
module FQ = Category FQ

-- Let's canonicalize all of the morphisms with domain `a`
data FromA : ∀ o → FQ [ a , o ] → Type ℓ-zero where
  cons : ∀ gen
       → ∀ {e} → FromA (dom gen) e
       → FromA (cod gen) ((η QUIVER <$g> gen) ∘⟨ FQ ⟩ e)
  nil  : FromA a FQ.id

forget : ∀ {o} {e} → FromA o e → List MOR
forget (cons gen fA) = gen ∷ forget fA
forget nil = []

-- | I think someone made a macro for this in the 1lab recently?
isSetFromA : ∀ {o e} → isSet (FromA o e)
isSetFromA {o}{e} = isSetRetract {B = IW S P inX (o , e)}
  encode
  decode
  retracts
  (isOfHLevelSuc-IW 1 isSetS (o , e))
  where
    -- The Index
    X = Σ[ o ∈ OB ] FQ [ a , o ]
    -- The data in the constructors besides subtrees
    S : X → Type _
    S x =
      -- nil
      ((a , FQ.id) ≡ x)
      ⊎ -- cons
      (Σ[ gen ∈ MOR ] Σ[ e' ∈ FQ [ a , dom gen ] ]
        (cod gen , ((η QUIVER <$g> gen) ∘⟨ FQ ⟩ e')) ≡ x)
    -- The type of subtrees of a constructor
    P : (x : X) → S x → Type _
    P _ = Sum.rec (λ _ → ⊥) (λ _ → Unit)
    -- The index of the subtrees
    inX : ∀ x (s : S x) → P x s → X
    inX x = Sum.elim
      (λ _ → Empty.elim)
      λ (gen , (e' , _)) tt →
        (dom gen , e')

    W : (o : OB) (e : FQ [ a , o ]) → Type _
    W = λ o e → IW S P inX (o , e)

    encode : ∀ {o}{e} → FromA o e → W o e
    encode nil = node (inl refl) Empty.elim
    encode (cons gen {e'} l) = node (inr (gen , (e' , refl))) λ _ → encode l

    decode : ∀ {o}{e} → W o e → FromA o e
    decode (node (inl p) subtree) =
      subst (λ (o , e) → FromA o e) p FromA.nil
    decode (node (inr (gen , (e' , q))) subtree) =
      subst (λ (o , e) → FromA o e) q (cons gen {e = e'} (decode (subtree tt)))

    retracts : ∀ {o}{e} → (nf : FromA o e) → decode (encode nf) ≡ nf
    retracts nil = transportRefl nil
    retracts (cons gen nf) =
      transportRefl (cons gen (decode (encode nf)))
      ∙ cong (cons gen) (retracts nf)

    isSetS : ∀ x → isSet (S x)
    isSetS x =
      isSet⊎
        (isOfHLevelPath 2 (isSetΣ isSetOB λ _ → FQ.isSetHom) _ _)
        (isSetΣ isSetMOR
          (λ _ → isSetΣ
            FQ.isSetHom
            (λ _ → isOfHLevelPath 2 (isSetΣ isSetOB (λ _ → FQ.isSetHom)) _ _)))

-- Here is our goal
canonicalize : ∀ o → (e : FQ [ a , o ]) → FromA o e
canonicalize = λ o e → subst (FromA o) (FQ.⋆IdL e) (S.F-hom e FQ.id nil) where
  A-pts : Functor FQ (SET ℓ-zero)
  A-pts = FQ [ a ,-]

  LogFam : Categoryᴰ FQ _ _
  LogFam = Disp.reindex (SETᴰ ℓ-zero ℓ-zero) A-pts

  S : Disp.Section LogFam
  S = Free.elim QUIVER (record { F-ob = λ o e → (FromA o e) , isSetFromA
                               ; F-hom = λ m e l → cons m l })
  module S = Disp.Section S

private
  _ : forget (canonicalize a FQ.id)
      ≡ []
  _ = refl

  -- The following two should be refl without length, but length is
  -- enough.
  _ : length (forget (canonicalize a (FQ.id ∘⟨ FQ ⟩ ↑ h)))
      ≡ length (h ∷ [])
  _ = refl

  _ : length
      (forget (canonicalize a ((↑ h ∘⟨ FQ ⟩ (↑ g ∘⟨ FQ ⟩ FQ.id)) ∘⟨ FQ ⟩ ↑ f)))
      ≡ length (h ∷ g ∷ f ∷ [])
  _ = refl
