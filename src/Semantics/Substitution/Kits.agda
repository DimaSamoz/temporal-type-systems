
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

open import CategoryTheory.Instances.Reactive renaming (top to ⊤)
open import TemporalOps.Diamond using (◇_)
open import CategoryTheory.Categories

open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality as ≡
    using (_≡_ ; refl)


-- Semantic interpretation of kits, grouping together
-- lemmas for the kit operations
record ⟦Kit⟧ {𝒮 : Schema} (k : Kit 𝒮) : Set where
    open Kit k
    field
        -- Interpretation of the syntactic entity of the given scheme
        ⟦_⟧ : ∀{A Δ} -> 𝒮 Δ A -> ⟦ Δ ⟧ₓ ⇴ ⟦ A ⟧ⱼ
        -- Variable conversion lemma
        ⟦𝓋⟧ : ∀ A Δ
           -> (n : ℕ) (⟦Δ⟧ : ⟦ Δ ⟧ₓ n) (⟦A⟧ : ⟦ A ⟧ⱼ n)
           -> ⟦ 𝓋 {Δ ,, A} top ⟧ n (⟦Δ⟧ , ⟦A⟧) ≡ ⟦A⟧
        -- Term conversion lemma
        ⟦𝓉⟧ : ∀{A Δ} (T : 𝒮 Δ A)
           -> (n : ℕ) (⟦Δ⟧ : ⟦ Δ ⟧ₓ n)
           -> ⟦ 𝓉 T ⟧ₘ n ⟦Δ⟧ ≡ ⟦ T ⟧ n ⟦Δ⟧
        -- Weakening map lemma
        ⟦𝓌⟧ : ∀ B {Δ A} (T : 𝒮 Δ A)
           -> (n : ℕ) (⟦Δ⟧ : ⟦ Δ ⟧ₓ n) (⟦B⟧ : ⟦ B ⟧ⱼ n)
           -> ⟦ 𝓌 {B} T ⟧ n (⟦Δ⟧ , ⟦B⟧) ≡ ⟦ T ⟧ n ⟦Δ⟧
        -- Context stabilisation lemma
        ⟦𝒶⟧ : ∀{A Δ} (T : 𝒮 Δ (A always))
           -> (n l : ℕ) (⟦Δ⟧ : ⟦ Δ ⟧ₓ n)
           -> ⟦ 𝒶 T ⟧ l (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ l) ≡ ⟦ T ⟧ n ⟦Δ⟧

-- | Interpretation of substitutions and combinators
module ⟦K⟧ {𝒮} {k : Kit 𝒮} (⟦k⟧ : ⟦Kit⟧ k) where
    open ⟦Kit⟧ ⟦k⟧
    open Kit k

    -- Denotation of substitutions as a map between contexts
    ⟦subst⟧ : ∀{Γ Δ} -> Subst 𝒮 Γ Δ -> ⟦ Δ ⟧ₓ ⇴ ⟦ Γ ⟧ₓ
    ⟦subst⟧ ● n ⟦Γ⟧ = ⊤.tt
    ⟦subst⟧ (σ ▸ T) n ⟦Γ⟧ = ⟦subst⟧ σ n ⟦Γ⟧ , ⟦ T ⟧ n ⟦Γ⟧

    -- Denotation of weakening
    ⟦⁺⟧ : ∀ A {Γ Δ} -> (σ : Subst 𝒮 Γ Δ)
       -> (n : ℕ) -> (⟦Δ⟧ : ⟦ Δ ⟧ₓ n) -> (⟦A⟧ : ⟦ A ⟧ⱼ n)
       -> ⟦subst⟧ (_⁺_ {A} σ k) n (⟦Δ⟧ , ⟦A⟧) ≡ ⟦subst⟧ σ n ⟦Δ⟧
    ⟦⁺⟧ A ● n ⟦Δ⟧ ⟦A⟧ = refl
    ⟦⁺⟧ A (_▸_ {B} σ T) n ⟦Δ⟧ ⟦A⟧ rewrite ⟦⁺⟧ A σ n ⟦Δ⟧ ⟦A⟧
                                      | ⟦𝓌⟧ A T n ⟦Δ⟧ ⟦A⟧ = refl

    -- Denotation of lifting
    ⟦↑⟧ : ∀ A {Δ Γ} -> (σ : Subst 𝒮 Γ Δ)
       -> (n : ℕ) -> (⟦Δ⟧ : ⟦ Δ ⟧ₓ n) -> (⟦A⟧ : ⟦ A ⟧ⱼ n)
       -> ⟦subst⟧ (_↑_ {A} σ k) n (⟦Δ⟧ , ⟦A⟧) ≡ (⟦subst⟧ σ n ⟦Δ⟧ , ⟦A⟧)
    ⟦↑⟧ A {Δ} ● n ⟦Δ⟧ ⟦A⟧ rewrite ⟦𝓋⟧ A Δ n ⟦Δ⟧ ⟦A⟧ = refl
    ⟦↑⟧ A {Δ} (σ ▸ T) n ⟦Δ⟧ ⟦A⟧
        rewrite ⟦⁺⟧ A σ n ⟦Δ⟧ ⟦A⟧
              | ⟦𝓌⟧ A T n ⟦Δ⟧ ⟦A⟧
              | ⟦𝓋⟧ A Δ n ⟦Δ⟧ ⟦A⟧ = refl

    -- Denotation of stabilisation idempotence
    ⟦ˢˢ⟧ : ∀ Γ -> (m n l : ℕ) -> (⟦Γ⟧ : (⟦ Γ ⟧ₓ) l)
      -> ⟦subst⟧ (Γ ˢˢₛ k) n (⟦ Γ ˢ ⟧ˢₓ m (⟦ Γ ⟧ˢₓ l ⟦Γ⟧ m) n)
       ≡ ⟦ Γ ⟧ˢₓ l ⟦Γ⟧ n
    ⟦ˢˢ⟧ ∙ m n l ⟦Γ⟧ = refl
    ⟦ˢˢ⟧ (Γ ,, B now) m n l (⟦Γ⟧ , ⟦B⟧) = ⟦ˢˢ⟧ Γ m n l ⟦Γ⟧
    ⟦ˢˢ⟧ (Γ ,, B always) m n l (⟦Γ⟧ , ⟦□B⟧)
        rewrite ⟦𝓋⟧ (B always) (Γ ˢ ˢ) n (⟦ Γ ˢ ⟧ˢₓ m (⟦ Γ ⟧ˢₓ l ⟦Γ⟧ m) n) ⟦□B⟧
              | ⟦⁺⟧ (B always) (Γ ˢˢₛ k) n (⟦ Γ ˢ ⟧ˢₓ m (⟦ Γ ⟧ˢₓ l ⟦Γ⟧ m) n) ⟦□B⟧
        = ≡.cong (_, ⟦□B⟧) (⟦ˢˢ⟧ Γ m n l ⟦Γ⟧)

    -- Denotation of identity substitution
    ⟦idₛ⟧ : ∀{Γ} (n : ℕ) (⟦Γ⟧ : ⟦ Γ ⟧ₓ n)
        -> ⟦subst⟧ (idₛ {Γ} k) n ⟦Γ⟧ ≡ ⟦Γ⟧
    ⟦idₛ⟧ {∙} n ⟦Γ⟧ = refl
    ⟦idₛ⟧ {Γ ,, A} n (⟦Γ⟧ , ⟦A⟧)
        rewrite ⟦⁺⟧ A {Γ} (idₛ k) n ⟦Γ⟧ ⟦A⟧
              | ⟦idₛ⟧ {Γ} n ⟦Γ⟧
              | ⟦𝓋⟧ A Γ n ⟦Γ⟧ ⟦A⟧ = refl

    -- | Commutation lemmas

    -- Interpretation of substitution and context stabilisation
    -- can be commuted
    ⟦subst⟧-⟦⟧ˢₓ : ∀{Γ Δ} -> (σ : Subst 𝒮 Γ Δ)
              -> (n l : ℕ) -> (⟦Δ⟧ : ⟦ Δ ⟧ₓ n)
              -> ⟦subst⟧ (σ ↓ˢ k) l (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ l)
               ≡ ⟦ Γ ⟧ˢₓ n (⟦subst⟧ σ n ⟦Δ⟧) l
    ⟦subst⟧-⟦⟧ˢₓ ● n l ⟦Δ⟧ = refl
    ⟦subst⟧-⟦⟧ˢₓ (_▸_ {x now} σ T) n l ⟦Δ⟧ = ⟦subst⟧-⟦⟧ˢₓ σ n l ⟦Δ⟧
    ⟦subst⟧-⟦⟧ˢₓ (_▸_ {x always} σ T) n l ⟦Δ⟧
        rewrite ⟦subst⟧-⟦⟧ˢₓ σ n l ⟦Δ⟧
              | ⟦𝒶⟧ T n l ⟦Δ⟧ = refl

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
        rewrite ⟦↑⟧ (A now) (_↑_ {Event B now} (σ ↓ˢ k) k) l (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ l , ⟦◇B⟧) ⟦A⟧
              | ⟦↑⟧ (Event B now) (σ ↓ˢ k) l (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ l) ⟦◇B⟧
              | ⟦subst⟧-⟦⟧ˢₓ σ n l ⟦Δ⟧ = refl
    ⟦subst⟧-⟦select⟧ {Δ} A B σ n l (inj₁ (inj₂ (⟦◇A⟧ , ⟦B⟧))) ⟦Δ⟧
        rewrite ⟦↑⟧ (B now) (_↑_ {Event A now} (σ ↓ˢ k) k) l (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ l , ⟦◇A⟧) ⟦B⟧
              | ⟦↑⟧ (Event A now) (σ ↓ˢ k) l (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ l) ⟦◇A⟧
              | ⟦subst⟧-⟦⟧ˢₓ σ n l ⟦Δ⟧ = refl
    ⟦subst⟧-⟦select⟧ {Δ} A B σ n l (inj₂ (⟦A⟧ , ⟦B⟧)) ⟦Δ⟧
        rewrite ⟦↑⟧ (B now) (_↑_ {A now} (σ ↓ˢ k) k) l (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ l , ⟦A⟧) ⟦B⟧
              | ⟦↑⟧ (A now) (σ ↓ˢ k) l (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ l) ⟦A⟧
              | ⟦subst⟧-⟦⟧ˢₓ σ n l ⟦Δ⟧ = refl
