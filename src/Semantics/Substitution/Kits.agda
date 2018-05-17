
-- Semantics of syntactic kits and explicit substitutions
module Semantics.Substitution.Kits where

open import Syntax.Types
open import Syntax.Context renaming (_,_ to _,,_)
open import Syntax.Terms
open import Syntax.Substitution.Kits

open import Semantics.Types
open import Semantics.Context
open import Semantics.Select
open import Semantics.Terms

open import CategoryTheory.Categories
open import CategoryTheory.Instances.Reactive renaming (top to Top)
open import CategoryTheory.Functor
open import CategoryTheory.Comonad
open import TemporalOps.Diamond
open import TemporalOps.Box

open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality as ≡
    using (_≡_ ; refl)

open Comonad W-□
private module F-□ = Functor F-□

-- Semantic interpretation of kits, grouping together
-- lemmas for the kit operations
record ⟦Kit⟧ {𝒮 : Schema} (k : Kit 𝒮) : Set where
    open Kit k
    field
        -- Interpretation of the syntactic entity of the given scheme
        ⟦_⟧ : ∀{A Δ} -> 𝒮 Δ A -> ⟦ Δ ⟧ₓ ⇴ ⟦ A ⟧ⱼ
        -- Variable conversion lemma
        ⟦𝓋⟧ : ∀ A Δ
           -> ⟦ 𝓋 {Δ ,, A} top ⟧ ≈ π₂
        -- Term conversion lemma
        ⟦𝓉⟧ : ∀{A Δ} (T : 𝒮 Δ A)
           -> ⟦ 𝓉 T ⟧ₘ ≈ ⟦ T ⟧
        -- Weakening map lemma
        ⟦𝓌⟧ : ∀ B {Δ A} (T : 𝒮 Δ A)
           -> ⟦ 𝓌 {B} T ⟧ ≈ ⟦ T ⟧ ∘ π₁
        -- Context stabilisation lemma
        ⟦𝒶⟧ : ∀{A Δ} (T : 𝒮 Δ (A always))
           -> F-□.fmap ⟦ 𝒶 T ⟧ ∘ ⟦ Δ ⟧ˢₓ-□ ≈ δ.at ⟦ A ⟧ₜ ∘ ⟦ T ⟧

-- | Interpretation of substitutions and combinators
module ⟦K⟧ {𝒮} {k : Kit 𝒮} (⟦k⟧ : ⟦Kit⟧ k) where
    open ⟦Kit⟧ ⟦k⟧
    open Kit k
    -- Denotation of substitutions as a map between contexts
    ⟦subst⟧ : ∀{Γ Δ} -> Subst 𝒮 Γ Δ -> ⟦ Δ ⟧ₓ ⇴ ⟦ Γ ⟧ₓ
    ⟦subst⟧ ●       = !
    ⟦subst⟧ (σ ▸ T) = ⟨ ⟦subst⟧ σ , ⟦ T ⟧ ⟩

    -- Denotation of weakening
    ⟦⁺⟧ : ∀ A {Γ Δ} -> (σ : Subst 𝒮 Γ Δ)
       -> ⟦subst⟧ (_⁺_ {A} σ k) ≈ ⟦subst⟧ σ ∘ π₁
    ⟦⁺⟧ A ● = refl
    ⟦⁺⟧ A (_▸_ {B} σ T) {n} {a} rewrite ⟦⁺⟧ A σ {n} {a}
                                     | ⟦𝓌⟧ A T {n} {a} = refl
    -- Denotation of lifting
    ⟦↑⟧ : ∀ A {Δ Γ} -> (σ : Subst 𝒮 Γ Δ)
       -> ⟦subst⟧ (_↑_ {A} σ k) ≈ (⟦subst⟧ σ * id)
    ⟦↑⟧ A {Δ} ● {n} {a} rewrite ⟦𝓋⟧ A Δ {n} {a} = refl
    ⟦↑⟧ A {Δ} (σ ▸ T) {n} {a} rewrite ⟦⁺⟧ A σ {n} {a}
                                   | ⟦𝓌⟧ A T {n} {a}
                                   | ⟦𝓋⟧ A Δ {n} {a} = refl

    -- Denotation of stabilisation idempotence
    ⟦ˢˢ⟧ : ∀ Γ -> F-□.fmap (⟦subst⟧ (Γ ˢˢₛ k)) ∘ ⟦ Γ ˢ ⟧ˢₓ-□ ∘ ⟦ Γ ⟧ˢₓ ≈ ⟦ Γ ⟧ˢₓ-□
    ⟦ˢˢ⟧ ∙ = refl
    ⟦ˢˢ⟧ (Γ ,, B now) = ⟦ˢˢ⟧ Γ
    ⟦ˢˢ⟧ (Γ ,, B always) {n} {⟦Γˢ⟧ , □⟦B⟧} = ext lemma
        where
        lemma : ∀ l → (⟦subst⟧ (_⁺_ {B always} (Γ ˢˢₛ k) k) l (⟦ Γ ˢ ⟧ˢₓ-□ n (⟦ Γ ⟧ˢₓ n ⟦Γˢ⟧) l , □⟦B⟧) ,
                                   ⟦ 𝓋 {Γ ˢ ˢ ,, B always}{B always} top ⟧ l (⟦ Γ ˢ ⟧ˢₓ-□ n (⟦ Γ ⟧ˢₓ n ⟦Γˢ⟧) l , □⟦B⟧))
                            ≡ (⟦ Γ ⟧ˢₓ-□ n ⟦Γˢ⟧ l , □⟦B⟧)
        lemma l rewrite ⟦𝓋⟧ (B always) (Γ ˢ ˢ) {l} {⟦ Γ ˢ ⟧ˢₓ-□ n (⟦ Γ ⟧ˢₓ n ⟦Γˢ⟧) l , □⟦B⟧}
                      | ⟦⁺⟧ (B always) (Γ ˢˢₛ k) {l} {(⟦ Γ ˢ ⟧ˢₓ-□ n (⟦ Γ ⟧ˢₓ n ⟦Γˢ⟧) l , □⟦B⟧)}
                      | □-≡ n l (⟦ˢˢ⟧ Γ {n} {⟦Γˢ⟧}) l = refl

    -- Denotation of identity substitution
    ⟦idₛ⟧ : ∀ {Γ} -> ⟦subst⟧ (idₛ {Γ} k) ≈ id
    ⟦idₛ⟧ {∙} = refl
    ⟦idₛ⟧ {Γ ,, A} {n} {⟦Γ⟧ , ⟦A⟧}
        rewrite ⟦⁺⟧ A {Γ} (idₛ k) {n} {⟦Γ⟧ , ⟦A⟧}
              | ⟦idₛ⟧ {Γ} {n} {⟦Γ⟧}
              | ⟦𝓋⟧ A Γ {n} {⟦Γ⟧ , ⟦A⟧} = refl

    -- Simplified context stabilisation lemma for non-boxed stabilisation
    ⟦𝒶⟧′ : ∀{A Δ} (T : 𝒮 Δ (A always))
       -> ⟦ 𝒶 T ⟧ ∘ ⟦ Δ ⟧ˢₓ ≈ ⟦ T ⟧
    ⟦𝒶⟧′ {A} {Δ} T {n} {⟦Δ⟧} rewrite ⟦⟧ˢₓ-factor Δ {n} {⟦Δ⟧}
                           = □-≡ n n (⟦𝒶⟧ T) n

    -- | Commutativity lemmas

    -- Interpretation of substitution and context stabilisation
    -- can be commuted (naturality condition for ⟦_⟧ˢₓ)
    ⟦subst⟧-⟦⟧ˢₓ : ∀{Γ Δ} -> (σ : Subst 𝒮 Γ Δ)
              -> ⟦subst⟧ (σ ↓ˢ k) ∘ ⟦ Δ ⟧ˢₓ ≈ ⟦ Γ ⟧ˢₓ ∘ ⟦subst⟧ σ
    ⟦subst⟧-⟦⟧ˢₓ ● = refl
    ⟦subst⟧-⟦⟧ˢₓ (_▸_ {A now} σ T) = ⟦subst⟧-⟦⟧ˢₓ σ
    ⟦subst⟧-⟦⟧ˢₓ (_▸_ {A always} σ T) {n} {⟦Δ⟧}
        rewrite ⟦subst⟧-⟦⟧ˢₓ σ {n} {⟦Δ⟧}
              | ⟦𝒶⟧′ T {n} {⟦Δ⟧} = refl

    ⟦subst⟧-⟦⟧ˢₓ-□ : ∀{Γ Δ} -> (σ : Subst 𝒮 Γ Δ)
              -> F-□.fmap (⟦subst⟧ (σ ↓ˢ k)) ∘ ⟦ Δ ⟧ˢₓ-□
               ≈ ⟦ Γ ⟧ˢₓ-□ ∘ ⟦subst⟧ σ
    ⟦subst⟧-⟦⟧ˢₓ-□ ● = refl
    ⟦subst⟧-⟦⟧ˢₓ-□ (_▸_ {A now} σ T) = ⟦subst⟧-⟦⟧ˢₓ-□ σ
    ⟦subst⟧-⟦⟧ˢₓ-□ {Δ = Δ} (_▸_ {A always} {Γ} σ T) {n} {⟦Δ⟧} = ext lemma
        where
        lemma : ∀ l -> (F-□.fmap (⟦subst⟧ ((σ ▸ T) ↓ˢ k)) ∘ ⟦ Δ ⟧ˢₓ-□) n ⟦Δ⟧ l
                        ≡ (⟦ Γ ,, A always ⟧ˢₓ-□  ∘ ⟦subst⟧ (σ ▸ T)) n ⟦Δ⟧ l
        lemma l rewrite □-≡ n l (⟦𝒶⟧ T {n} {⟦Δ⟧}) l
                      | □-≡ n l (⟦subst⟧-⟦⟧ˢₓ-□ σ {n} {⟦Δ⟧}) l = refl

    -- Interpretation of substitution and selection can be commuted
    ⟦subst⟧-⟦select⟧ : ∀{Δ Γ C} A B -> (σ : Subst 𝒮 Γ Δ)
        -> (n l : ℕ)
        -> (c : (⟦ A ⟧ₜ ⊗ ◇ ⟦ B ⟧ₜ ⊕ ◇ ⟦ A ⟧ₜ ⊗ ⟦ B ⟧ₜ ⊕ ⟦ A ⟧ₜ ⊗ ⟦ B ⟧ₜ) l)
        -> (⟦Δ⟧ : ⟦ Δ ⟧ₓ n)
        -> {⟦C₁⟧ : ⟦ Γ ˢ ⟧ₓ ⊗ ◇ ⟦ B ⟧ₜ ⊗ ⟦ A ⟧ₜ ⇴ ◇ ⟦ C ⟧ₜ}
        -> {⟦C₂⟧ : ⟦ Γ ˢ ⟧ₓ ⊗ ◇ ⟦ A ⟧ₜ ⊗ ⟦ B ⟧ₜ ⇴ ◇ ⟦ C ⟧ₜ}
        -> {⟦C₃⟧ : ⟦ Γ ˢ ⟧ₓ ⊗   ⟦ A ⟧ₜ ⊗ ⟦ B ⟧ₜ ⇴ ◇ ⟦ C ⟧ₜ}
        -> (⟦select⟧ Δ A B C n ⟦Δ⟧
            (⟦C₁⟧ ∘ (⟦subst⟧ (_↑_ {A now} (_↑_ {Event B now} (σ ↓ˢ k) k) k)))
            (⟦C₂⟧ ∘ (⟦subst⟧ (_↑_ {B now} (_↑_ {Event A now} (σ ↓ˢ k) k) k)))
            (⟦C₃⟧ ∘ (⟦subst⟧ (_↑_ {B now} (_↑_ {A now}       (σ ↓ˢ k) k) k))) l c)
         ≡ (⟦select⟧ Γ A B C n (⟦subst⟧ σ n ⟦Δ⟧) ⟦C₁⟧ ⟦C₂⟧ ⟦C₃⟧ l c)

    ⟦subst⟧-⟦select⟧ {Δ} A B σ n l (inj₁ (inj₁ (⟦A⟧ , ⟦◇B⟧))) ⟦Δ⟧
        rewrite ⟦↑⟧ (A now) (_↑_ {Event B now} (σ ↓ˢ k) k) {l} {(⟦ Δ ⟧ˢₓ-□ n ⟦Δ⟧ l , ⟦◇B⟧) , ⟦A⟧}
              | ⟦↑⟧ (Event B now) (σ ↓ˢ k) {l} {⟦ Δ ⟧ˢₓ-□ n ⟦Δ⟧ l , ⟦◇B⟧}
              | □-≡ n l (⟦subst⟧-⟦⟧ˢₓ-□ σ {n} {⟦Δ⟧}) l = refl
    ⟦subst⟧-⟦select⟧ {Δ} A B σ n l (inj₁ (inj₂ (⟦◇A⟧ , ⟦B⟧))) ⟦Δ⟧
        rewrite ⟦↑⟧ (B now) (_↑_ {Event A now} (σ ↓ˢ k) k) {l} {(⟦ Δ ⟧ˢₓ-□ n ⟦Δ⟧ l , ⟦◇A⟧) , ⟦B⟧}
              | ⟦↑⟧ (Event A now) (σ ↓ˢ k) {l} {⟦ Δ ⟧ˢₓ-□ n ⟦Δ⟧ l , ⟦◇A⟧}
              | □-≡ n l (⟦subst⟧-⟦⟧ˢₓ-□ σ {n} {⟦Δ⟧}) l = refl
    ⟦subst⟧-⟦select⟧ {Δ} A B σ n l (inj₂ (⟦A⟧ , ⟦B⟧)) ⟦Δ⟧
        rewrite ⟦↑⟧ (B now) (_↑_ {A now} (σ ↓ˢ k) k) {l} {(⟦ Δ ⟧ˢₓ-□ n ⟦Δ⟧ l , ⟦A⟧) , ⟦B⟧}
              | ⟦↑⟧ (A now) (σ ↓ˢ k) {l} {⟦ Δ ⟧ˢₓ-□ n ⟦Δ⟧ l , ⟦A⟧}
              | □-≡ n l (⟦subst⟧-⟦⟧ˢₓ-□ σ {n} {⟦Δ⟧}) l = refl

    -- ⟦subst⟧-⟦select⟧ : ∀{Δ Γ C} A B -> (σ : Subst 𝒮 Γ Δ)
    --     -> {⟦C₁⟧ : ⟦ Γ ˢ ⟧ₓ ⊗ ◇ ⟦ B ⟧ₜ ⊗ ⟦ A ⟧ₜ ⇴ ◇ ⟦ C ⟧ₜ}
    --     -> {⟦C₂⟧ : ⟦ Γ ˢ ⟧ₓ ⊗ ◇ ⟦ A ⟧ₜ ⊗ ⟦ B ⟧ₜ ⇴ ◇ ⟦ C ⟧ₜ}
    --     -> {⟦C₃⟧ : ⟦ Γ ˢ ⟧ₓ ⊗   ⟦ A ⟧ₜ ⊗ ⟦ B ⟧ₜ ⇴ ◇ ⟦ C ⟧ₜ}
    --     -> (⟦select⟧ Δ A B C
    --         (⟦C₁⟧ ∘ (⟦subst⟧ (_↑_ {A now} (_↑_ {Event B now} (σ ↓ˢ k) k) k)))
    --         (⟦C₂⟧ ∘ (⟦subst⟧ (_↑_ {B now} (_↑_ {Event A now} (σ ↓ˢ k) k) k)))
    --         (⟦C₃⟧ ∘ (⟦subst⟧ (_↑_ {B now} (_↑_ {A now}       (σ ↓ˢ k) k) k))))
    --      ≈ ⟦select⟧ Γ A B C ⟦C₁⟧ ⟦C₂⟧ ⟦C₃⟧ ∘ (⟦subst⟧ (σ ↓ˢ k) * id)
    -- ⟦subst⟧-⟦select⟧ A B σ {n = n} {⟦Δ⟧ , inj₁ (inj₁ (⟦A⟧ , ⟦◇B⟧))}
    --     rewrite ⟦↑⟧ (A now) (_↑_ {Event B now} (σ ↓ˢ k) k) {n} {(⟦Δ⟧ , ⟦◇B⟧) , ⟦A⟧}
    --           | ⟦↑⟧ (Event B now) (σ ↓ˢ k) {n} {⟦Δ⟧ , ⟦◇B⟧} = refl
    -- ⟦subst⟧-⟦select⟧ A B σ {n = n} {⟦Δ⟧ , inj₁ (inj₂ (⟦B⟧ , ⟦◇A⟧))}
    --     rewrite ⟦↑⟧ (B now) (_↑_ {Event A now} (σ ↓ˢ k) k) {n} {(⟦Δ⟧ , ⟦B⟧) , ⟦◇A⟧}
    --           | ⟦↑⟧ (Event A now) (σ ↓ˢ k) {n} {⟦Δ⟧ , ⟦B⟧} = refl
    -- ⟦subst⟧-⟦select⟧ A B σ {n = n} {⟦Δ⟧ , inj₂ (⟦A⟧ , ⟦B⟧)}
    --     rewrite ⟦↑⟧ (B now) (_↑_ {A now} (σ ↓ˢ k) k) {n} {(⟦Δ⟧ , ⟦A⟧) , ⟦B⟧}
    --           | ⟦↑⟧ (A now) (σ ↓ˢ k) {n} {⟦Δ⟧ , ⟦A⟧} = refl
