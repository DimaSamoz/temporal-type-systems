
-- Instances of semantic kits
module Semantics.Substitution.Instances where

open import Syntax.Types
open import Syntax.Context renaming (_,_ to _,,_)
open import Syntax.Terms
open import Syntax.Substitution.Kits
open import Syntax.Substitution.Instances

open import Semantics.Types
open import Semantics.Context
open import Semantics.Select
open import Semantics.Terms
open import Semantics.Substitution.Kits
open import Semantics.Substitution.Traversal

open import CategoryTheory.Categories using (ext)
open import CategoryTheory.NatTrans
open import CategoryTheory.Functor
open import CategoryTheory.Monad
open import CategoryTheory.Comonad
open import CategoryTheory.Instances.Reactive renaming (top to ⊤)
open import TemporalOps.Diamond
open import TemporalOps.Box
open import TemporalOps.Common.Rewriting

open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality as ≅ using (_≅_)

open import Holes.Term using (⌞_⌟)
open import Holes.Cong.Propositional

open ≡-Reasoning
private module F-□ = Functor F-□
open Comonad W-□

-- Denotation of variable kits
⟦𝒱ar⟧ : ⟦Kit⟧ 𝒱ar
⟦𝒱ar⟧ = record
    { ⟦_⟧ = ⟦_⟧-var
    ; ⟦𝓋⟧ = λ A Δ → refl
    ; ⟦𝓉⟧ = ⟦𝓉⟧-var
    ; ⟦𝓌⟧ = λ B T → refl
    ; ⟦𝒶⟧ = ⟦𝒶⟧-var
    }
    where
    open Kit 𝒱ar
    ⟦_⟧-var : ∀{A Γ} → Var Γ A → ⟦ Γ ⟧ₓ ⇴ ⟦ A ⟧ⱼ
    ⟦ top ⟧-var n (_ , ⟦A⟧) = ⟦A⟧
    ⟦ pop v ⟧-var n (⟦Γ⟧ , _) = ⟦ v ⟧-var n ⟦Γ⟧

    ⟦𝓉⟧-var : ∀{A Γ} → (x : Var Γ A)
          -> ⟦ 𝓉 x ⟧ₘ ≈ ⟦ x ⟧-var
    ⟦𝓉⟧-var {A now} top = refl
    ⟦𝓉⟧-var {A always} top = refl
    ⟦𝓉⟧-var {A now} (pop x) = ⟦𝓉⟧-var x
    ⟦𝓉⟧-var {A always} (pop x) = ⟦𝓉⟧-var x

    ⟦𝒶⟧-var : ∀{A Δ} → (x : Var Δ (A always))
           -> F-□.fmap ⟦ 𝒶 x ⟧-var ∘ ⟦ Δ ˢ⟧□ ≈ δ.at ⟦ A ⟧ₜ ∘ ⟦ x ⟧-var
    ⟦𝒶⟧-var top = refl
    ⟦𝒶⟧-var (pop {B = B now} x) = ⟦𝒶⟧-var x
    ⟦𝒶⟧-var (pop {B = B always} x) = ⟦𝒶⟧-var x


-- Denotation of term kits
⟦𝒯erm⟧ : ⟦Kit⟧ 𝒯erm
⟦𝒯erm⟧ = record
    { ⟦_⟧ = ⟦_⟧ₘ
    ; ⟦𝓋⟧ = λ A Δ → refl
    ; ⟦𝓉⟧ = λ T → refl
    ; ⟦𝓌⟧ = ⟦𝓌⟧-term
    ; ⟦𝒶⟧ = ⟦𝒶⟧-term
    }
    where
    open Kit 𝒯erm
    open ⟦Kit⟧ ⟦𝒱ar⟧
    open K
    open ⟦K⟧ ⟦𝒱ar⟧

    ⟦𝓌⟧-term : ∀ B {Δ A} → (M : Term Δ A)
           -> ⟦ 𝓌 {B} M ⟧ₘ ≈ ⟦ M ⟧ₘ ∘ π₁
    ⟦𝓌⟧-term B {Δ} M {n} {⟦Δ⟧ , ⟦B⟧}
        rewrite traverse-sound ⟦𝒱ar⟧ (_⁺_ {B} (idₛ 𝒱ar) 𝒱ar) M {n} {⟦Δ⟧ , ⟦B⟧}
              | ⟦⁺⟧ B {Δ} (idₛ 𝒱ar) {n} {⟦Δ⟧ , ⟦B⟧}
              | ⟦idₛ⟧ {Δ} {n} {⟦Δ⟧} = refl

    ⟦𝒶⟧-term : ∀{A Δ} (M : Δ ⊢ A always)
           -> F-□.fmap ⟦ 𝒶 M ⟧ₘ ∘ ⟦ Δ ˢ⟧□ ≈ δ.at ⟦ A ⟧ₜ ∘ ⟦ M ⟧ₘ
    ⟦𝒶⟧-term {A} {∙} (var ())
    ⟦𝒶⟧-term {A} {∙} (stable M) = refl
    ⟦𝒶⟧-term {A} {Δ ,, B now} (var (pop x)) = ⟦𝒶⟧-term (var x)
    ⟦𝒶⟧-term {A} {Δ ,, B now} (stable M) = ⟦𝒶⟧-term {A} {Δ} (stable M)
    ⟦𝒶⟧-term {.B} {Δ ,, B always} (var top) = refl
    ⟦𝒶⟧-term {A} {Δ ,, B always} (var (pop x)) {n} {⟦Δ⟧ , □⟦B⟧} = ext lemma
        where
        lemma : ∀ l -> ⟦ traverse 𝒱ar (_⁺_ {B always} (idₛ 𝒱ar) 𝒱ar) (𝒶 (var x)) ⟧ₘ l (⟦ Δ ˢ⟧□ n ⟦Δ⟧ l , □⟦B⟧)
                     ≡ ⟦ var x ⟧ₘ n ⟦Δ⟧
        lemma l rewrite traverse-sound ⟦𝒱ar⟧ (_⁺_ {B always} (idₛ 𝒱ar) 𝒱ar) (𝒶 (var x)) {l} {⟦ Δ ˢ⟧□ n ⟦Δ⟧ l , □⟦B⟧}
                      | ⟦⁺⟧ (B always) {Δ ˢ} (idₛ 𝒱ar) {l} {⟦ Δ ˢ⟧□ n ⟦Δ⟧ l , □⟦B⟧}
                      | ⟦idₛ⟧ {Δ ˢ} {l} {⟦ Δ ˢ⟧□ n ⟦Δ⟧ l}
                      | □-≡ n l (⟦𝒶⟧-term (var x) {n} {⟦Δ⟧}) l = refl
    ⟦𝒶⟧-term {A} {Δ ,, B always} (stable M) {n} {⟦Δ⟧ , □⟦B⟧} = ext λ x → ext (lemma2 x)
        where
        lemma1 : ∀ Δ (n l m : ℕ) (⟦Δ⟧ : ⟦ Δ ⟧ₓ n)
                 -> (F-□.fmap ⟦ Δ ˢ ˢ⟧□ ∘ ⟦ Δ ˢ⟧□) n ⟦Δ⟧ l m
                  ≡ (F-□.fmap ⟦ Δ ˢ ˢ⟧ ∘ ⟦ Δ ˢ⟧□) n ⟦Δ⟧ m
        lemma1 Δ n l m ⟦Δ⟧ rewrite □-≡ l m (□-≡ n l (⟦ˢ⟧□-twice Δ {n} {⟦Δ⟧}) l) m
                = □-≡ n m (⟦ˢ⟧-comm Δ) m

        lemma2 : ∀ l j
              -> (F-□.fmap ⟦ 𝒶 {Δ ,, B always} (stable M) ⟧ₘ ∘ ⟦ Δ ,, B always ˢ⟧□) n (⟦Δ⟧ , □⟦B⟧) l j
               ≡ (δ.at ⟦ A ⟧ₜ ∘ ⟦ stable {Δ ,, B always} M ⟧ₘ) n (⟦Δ⟧ , □⟦B⟧) l j
        lemma2 l j =
            begin
                ⟦ subst (λ x → x ,, B always ⊢ A now) (ˢ-idemp′ Δ) M ⟧ₘ j (⟦ Δ ˢ ˢ⟧□ l (⟦ Δ ˢ⟧□ n ⟦Δ⟧ l) j  , □⟦B⟧)
            ≡⟨ cong (λ x → ⟦ subst (λ x → x ,, B always ⊢ A now) (ˢ-idemp′ Δ) M ⟧ₘ j (x , □⟦B⟧)) (lemma1 Δ n l j ⟦Δ⟧) ⟩
                ⟦ subst (λ x → x ,, B always ⊢ A now) (ˢ-idemp′ Δ) M ⟧ₘ j (⟦ Δ ˢ ˢ⟧ j (⟦ Δ ˢ⟧□ n ⟦Δ⟧ j) , □⟦B⟧)
            ≡⟨ cong (λ x → ⟦ subst (λ x → x ,, B always ⊢ A now) (ˢ-idemp′ Δ) M ⟧ₘ j (x , □⟦B⟧)) (⟦ˢ⟧-rew Δ n j ⟦Δ⟧) ⟩
                ⟦ subst (λ x → x ,, B always ⊢ A now) (ˢ-idemp′ Δ) M ⟧ₘ j (rew (⟦ˢ⟧-idemp Δ j) (⟦ Δ ˢ⟧□ n ⟦Δ⟧ j) , □⟦B⟧)
            ≅⟨ full-eq j M-eq (≅.sym (rew-to-≅ (⟦ˢ⟧-idemp Δ j))) □⟦B⟧ ⟩
                ⟦ M ⟧ₘ j (⟦ Δ ˢ⟧□ n ⟦Δ⟧ j , □⟦B⟧)
            ∎

         where
            ˢ-idemp′ : ∀ Γ -> Γ ˢ ≡ Γ ˢ ˢ
            ˢ-idemp′ Γ = sym (ˢ-idemp Γ)

            ⟦ˢ⟧-idemp : ∀ Δ n -> ⟦ Δ ˢ ⟧ₓ n ≡ ⟦ Δ ˢ ˢ ⟧ₓ n
            ⟦ˢ⟧-idemp Δ n = cong (λ x → ⟦ x ⟧ₓ n) (ˢ-idemp′ Δ)

            rew-lemma : ∀ Δ A n l ⟦Δ⟧ □⟦A⟧
                 -> (rew (cong (λ x → ⟦ x ⟧ₓ l) (ˢ-idemp′ Δ)) (⟦ Δ ˢ⟧□ n ⟦Δ⟧ l) , □⟦A⟧)
                  ≡ rew (cong (λ x → ⟦ x ⟧ₓ l) (ˢ-idemp′ (Δ ,, A always))) (⟦ Δ ˢ⟧□ n ⟦Δ⟧ l , □⟦A⟧)
            rew-lemma Δ A n l ⟦Δ⟧ □⟦A⟧ rewrite ˢ-idemp Δ = refl

            ⟦ˢ⟧-rew : ∀ Δ n l ⟦Δ⟧ -> ⟦ Δ ˢ ˢ⟧ l (⟦ Δ ˢ⟧□ n ⟦Δ⟧ l)
                                  ≡ rew (⟦ˢ⟧-idemp Δ l) (⟦ Δ ˢ⟧□ n ⟦Δ⟧ l)
            ⟦ˢ⟧-rew ∙ n l ⟦Δ⟧ = refl
            ⟦ˢ⟧-rew (Δ ,, A now) n l (⟦Δ⟧ , ⟦A⟧) = ⟦ˢ⟧-rew Δ n l ⟦Δ⟧
            ⟦ˢ⟧-rew (Δ ,, A always) n l (⟦Δ⟧ , □⟦A⟧)
                    rewrite ⟦ˢ⟧-rew Δ n l ⟦Δ⟧
                          | rew-lemma Δ A n l ⟦Δ⟧ □⟦A⟧ = refl

            M-eq : subst (λ x → x ,, B always ⊢ A now) (ˢ-idemp′ Δ) M  ≅ M
            M-eq = ≅.≡-subst-removable (λ x → x ,, B always ⊢ A now) (ˢ-idemp′ Δ) M

            full-eq : ∀ j {M₁ : Δ ˢ ˢ ,, B always ⊢ A now}
                          {M₂ : Δ ˢ ,, B always ⊢ A now}
                          {⟦Δ⟧₁ : ⟦ Δ ˢ ˢ ⟧ₓ j} {⟦Δ⟧₂ : ⟦ Δ ˢ ⟧ₓ j}
                          (p-M : M₁ ≅ M₂) (p-⟦Δ⟧ : ⟦Δ⟧₁ ≅ ⟦Δ⟧₂) □⟦B⟧
                   -> ⟦ M₁ ⟧ₘ j (⟦Δ⟧₁ , □⟦B⟧) ≅ ⟦ M₂ ⟧ₘ j (⟦Δ⟧₂ , □⟦B⟧)
            full-eq j p-M p-⟦Δ⟧ □⟦B⟧ rewrite ˢ-idemp Δ
                    = ≅.cong₂ ((λ x y → ⟦ x ⟧ₘ j (y , □⟦B⟧))) p-M p-⟦Δ⟧
