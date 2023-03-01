module Syntax.STLC.Semantics.Soundness where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf

open import NamedContext
open import UMP
open import NaturalModels.Cartesian
open import Syntax.STLC renaming (Tm to STm; Ty to STy)
open import Syntax.STLC.Semantics.Interpretation
open import Syntax.STLC.Semantics.Lindenbaum

private
  variable
    ℓ ℓ' ℓb ℓb' ℓc ℓc' ℓt ℓt' : Level
module _ {Σ₀ : Sig₀ ℓ}{Σ₁ : Sig₁ Σ₀ ℓ'}
         (S : SimplyTypedCategory ℓb ℓb' ℓt ℓt')
         (i₀ : Interp₀ Σ₀ S) (i₁ : Interp₁ {S = S} i₀ Σ₁)
         where
  open Category
  open STC-Functor
  open CartesianFunctor
  open UnivElt
  open isUniversal
  open Ctx
  open Sig₁

  open SimplyTypedCategory(S)
  open CartesianCategory(B)
  -- some abbreviations
  private
    Term = STm {Σ₀ = Σ₀} Σ₁
    Subst = STT-subst Σ₁

  ctx-sem : Ctx (STy Σ₀) → cat .ob
  ctx-sem = interpCtx {Σ₀ = Σ₀} {S = S} i₀

  term-sem : ∀ {Γ A} → Term Γ A → (Tm (i₀ A) ⟅ ctx-sem Γ ⟆) .fst
  term-sem (ivar x) =
    Tm-repr _ .element ⟨ π _ _ x ⟩S
  term-sem {Γ} (fun-app f γ) = i₁ f ⟨ γ~ ⟩S where
    γ~ : cat [ ctx-sem Γ , ctx-sem (Σ₁ .src f) ]
    γ~ = prod-I (varFinSet (Σ₁ .src f))
                (λ x → sole (i₀ (Σ₁ .src f .el x)))
                λ x → term-sem (γ x) /the-var

  subst-sem : ∀ {Δ Γ} → Subst Δ Γ → cat [ (ctx-sem Δ) , (ctx-sem Γ) ]
  subst-sem {Δ = Δ}{Γ} γ =
    prod-I (varFinSet Γ)
           (λ x → sole (i₀ (Γ .el x)))
           λ x → term-sem (γ x) /the-var

  private
    subst-sem-comp-ind : ∀ {Ξ Δ Γ} → (γ : Subst Δ Γ) (δ : Subst Ξ Δ)
                       → (∀ x → term-sem (γ x ⟨ δ ⟩) ≡ term-sem (γ x) ⟨ subst-sem δ ⟩S)
                       → subst-sem {Γ = Γ} (comp-subst {Γ = Γ} γ δ) ≡ (subst-sem γ ∘⟨ cat ⟩ subst-sem δ)
    subst-sem-comp-ind {Γ = Γ} γ δ IH =
      determined-by-elt (finite-products (varFinSet Γ) (λ x → sole (i₀ (Γ .el x))) .universal)
        (funExt (λ x →
          π _ _ x ∘⟨ cat ⟩ subst-sem ( λ x → γ x ⟨ δ ⟩)
            ≡⟨ π∘prod-I _ _ (λ x → term-sem (γ x ⟨ δ ⟩) /the-var) x ⟩
          term-sem (γ x ⟨ δ ⟩) /the-var
            ≡[ i ]⟨ IH x i /the-var ⟩
          (term-sem (γ x) ⟨ subst-sem δ ⟩S) /the-var -- M/x o γ = M ⟨ γ ⟩ / x
            ≡⟨ sym (/the-var⟨⟩S _ _) ⟩
          (term-sem (γ x) /the-var) ∘⟨ cat ⟩ subst-sem δ
            ≡[ i ]⟨ π∘prod-I (varFinSet Γ) _ (λ x → term-sem (γ x) /the-var) x (~ i) ∘⟨ cat ⟩ subst-sem δ ⟩
          ((π _ _ x) ∘⟨ cat ⟩ subst-sem γ) ∘⟨ cat ⟩ subst-sem δ
            ≡[ i ]⟨ cat .⋆Assoc (subst-sem δ) (subst-sem {Γ = Γ} γ) (π _ _ x) (~ i) ⟩
          (π _ _ x) ∘⟨ cat ⟩ (subst-sem γ ∘⟨ cat ⟩ subst-sem δ)
          ∎))

  compositional : ∀ {Δ Γ A} → (M : Term Γ A) → (γ : Subst Δ Γ)
                → term-sem (M ⟨ γ ⟩) ≡ term-sem M ⟨ subst-sem γ ⟩S
  compositional {Γ = Γ}{A} (ivar x) γ =
    term-sem (γ x)
      ≡⟨ sym (⟨/the-var⟩ (term-sem (γ x))) ⟩
    the-var ⟨ term-sem (γ x) /the-var ⟩S
      ≡[ i ]⟨ the-var ⟨ π∘prod-I (varFinSet Γ) (λ x → sole (i₀ (Γ .el x))) (λ x → term-sem (γ x) /the-var) x (~ i) ⟩S ⟩
    the-var ⟨ π (varFinSet Γ) _ x ∘⟨ cat ⟩ subst-sem γ ⟩S
      ≡⟨ ∘ᴾAssoc cat (Tm _) _ _ _ ⟩
    the-var ⟨ π _ _ x ⟩S ⟨ subst-sem γ ⟩S
    ∎
  compositional (fun-app f δ) γ =
    (i₁ f ⟨ subst-sem ( λ x → δ x ⟨ γ ⟩) ⟩S)
      ≡[ i ]⟨ i₁ f ⟨ subst-sem-comp-ind δ γ (λ x → compositional (δ x) γ) i ⟩S ⟩
    (i₁ f ⟨ subst-sem δ ∘⟨ cat ⟩ subst-sem γ ⟩S)
      ≡⟨ ∘ᴾAssoc cat (Tm _) _ _ _ ⟩
    i₁ f ⟨ subst-sem δ ⟩S ⟨ subst-sem γ ⟩S
    ∎

  subst-sem-comp : ∀ {Ξ Δ Γ} → (γ : Subst Δ Γ) (δ : Subst Ξ Δ)
                 → subst-sem {Γ = Γ} (comp-subst {Γ = Γ} γ δ) ≡ (subst-sem γ ∘⟨ cat ⟩ subst-sem δ)
  subst-sem-comp {Γ = Γ} γ δ = subst-sem-comp-ind γ δ (λ x → compositional (γ x) δ)


  -- Soundness says that we can translate any structure in the
  -- Lindenbaum algebra homomorphically into any CT structure.
  soundness : STC-Functor (Lindenbaum {Σ₀ = Σ₀}{Σ₁ = Σ₁}) S
  soundness .F-B .func .Functor.F-ob Γ = ctx-sem Γ
  soundness .F-B .func .Functor.F-hom {y = Γ} γ = subst-sem γ
  soundness .F-B .func .Functor.F-id {x = Γ} =
    {!!}
    -- (pi_i o [var] , pi_2 o [var]) = id
    --
    -- sym (S .B .finite-products ((Γ .var) , (Γ .isFinSetVar)) (λ x → sole S (i₀ (Γ .el x)))
    --        .universal .is-uniq {!!} {!!} (funExt (λ x →
    --        (S .B .cat [ (S .B .finite-products (Γ .var , Γ .isFinSetVar) (λ x₁ → sole S (i₀ (Γ .el x₁))) .element) ∘ᴾ⟨ (Πᴾ (S .B .cat) (Γ .var) (λ x₁ → S .B .cat [-, sole S (i₀ (Γ .el x₁)) ])) ⟩ S .B .cat .id ]) x
    --          ≡[ i ]⟨ ∘ᴾId (S .B .cat) _ ((S .B .finite-products (Γ .var , Γ .isFinSetVar) (λ x₁ → sole S (i₀ (Γ .el x₁))) .element)) i x ⟩
    --        (S .B .finite-products (Γ .var , Γ .isFinSetVar) (λ x₁ → sole S (i₀ (Γ .el x₁))) .element) x
    --          ≡⟨ {!!} ⟩
    --        {!!} ∎
           -- S .B .cat [ {!!} ∘ᴾ⟨ {!_!} ⟩ {!!} ] ≡⟨ {!!} ⟩ {!!} ∎
           -- S .Tm-repr (i₀ (Γ .el x)) .universal .is-uniq {!!} {!!}
           -- (S .B .cat [ (S .Tm-repr (i₀ (Γ .el x)) .element) ∘ᴾ⟨ (S .Tm (i₀ (Γ .el x))) ⟩
           -- {!S .B .cat [ ? ∘ᴾ⟨ ? ⟩ ]!} ]
           -- ≡⟨ {!!} ⟩
           -- S .B .cat [
           -- (S .Tm-repr (i₀ (Γ .el x)) .element) ∘ᴾ⟨ (S .Tm (i₀ (Γ .el x))) ⟩
           -- (π (S .B) (Γ .var , Γ .isFinSetVar) (λ x₁ → sole S (i₀ (Γ .el x₁))) x)
           -- ] ∎)

           -- {!!} .universal .is-uniq {!!} {!!} {!!}
           -- )))
  soundness .F-B .func .Functor.F-seq δ γ = subst-sem-comp γ δ
  soundness .F-B .preserves-fin-products = {!!}
  soundness .F-Ty = i₀
  soundness .F-Tm A .NatTrans.N-ob Γ (lift M) = lift (term-sem M)
  soundness .F-Tm A .NatTrans.N-hom γ = funExt λ (lift M) → cong lift (compositional M γ)
  soundness .F-Tm-repr = {!!}
