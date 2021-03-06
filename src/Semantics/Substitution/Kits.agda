
-- Semantics of syntactic kits and explicit substitutions
module Semantics.Substitution.Kits where

open import Syntax.Types
open import Syntax.Context renaming (_,_ to _,,_)
open import Syntax.Terms
open import Syntax.Substitution.Kits

open import Semantics.Types
open import Semantics.Context
open import Semantics.Terms

open import CategoryTheory.Categories
open import CategoryTheory.Instances.Reactive renaming (top to Top)
open import CategoryTheory.Functor
open import CategoryTheory.Comonad
open import TemporalOps.Diamond
open import TemporalOps.Box
open import TemporalOps.Linear

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
           -> F-□.fmap ⟦ 𝒶 T ⟧ ∘ ⟦ Δ ˢ⟧□ ≈ δ.at ⟦ A ⟧ₜ ∘ ⟦ T ⟧

-- | Interpretation of substitutions and combinators
module ⟦K⟧ {𝒮} {k : Kit 𝒮} (⟦k⟧ : ⟦Kit⟧ k) where
    open ⟦Kit⟧ ⟦k⟧
    open Kit k

    -- Denotation of substitutions as a map between contexts
    ⟦subst⟧ : ∀{Γ Δ} -> Subst 𝒮 Γ Δ -> ⟦ Δ ⟧ₓ ⇴ ⟦ Γ ⟧ₓ
    ⟦subst⟧ ●       = !
    ⟦subst⟧ (σ ▸ T) = ⟨ ⟦subst⟧ σ , ⟦ T ⟧ ⟩

    -- Simplified context stabilisation lemma for non-boxed stabilisation
    ⟦𝒶⟧′ : ∀{A Δ} (T : 𝒮 Δ (A always))
       -> ⟦ 𝒶 T ⟧ ∘ ⟦ Δ ˢ⟧ ≈ ⟦ T ⟧
    ⟦𝒶⟧′ {A} {Δ} T {n} {⟦Δ⟧} rewrite ⟦ˢ⟧-factor Δ {n} {⟦Δ⟧}
                           = □-≡ n n (⟦𝒶⟧ T) n


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

    -- Denotation of stabilisation (naturality condition for ⟦_ˢ⟧□)
    ⟦↓ˢ⟧ : ∀ {Γ Δ} -> (σ : Subst 𝒮 Γ Δ)
       -> F-□.fmap (⟦subst⟧ (σ ↓ˢ k)) ∘ ⟦ Δ ˢ⟧□ ≈ ⟦ Γ ˢ⟧□ ∘ ⟦subst⟧ σ
    ⟦↓ˢ⟧ ● = refl
    ⟦↓ˢ⟧ (_▸_ {A now} σ T) {n} {a} rewrite ⟦↓ˢ⟧ σ {n} {a} = refl
    ⟦↓ˢ⟧ {Δ = Δ} (_▸_ {A always}{Γ} σ T) {n} {a}  = ext lemma
        where
        lemma : ∀ l -> (F-□.fmap (⟦subst⟧ ((σ ▸ T) ↓ˢ k)) ∘ ⟦ Δ ˢ⟧□) n a l
                     ≡ (⟦ Γ ,, A always ˢ⟧□ ∘ ⟦subst⟧ (σ ▸ T)) n a l
        lemma l rewrite □-≡ n l (⟦↓ˢ⟧ σ {n} {a}) l
                      | □-≡ n l (⟦𝒶⟧ T {n} {a}) l = refl

    -- Simplified denotation of stabilisation
    ⟦↓ˢ⟧′ : ∀ {Γ Δ} -> (σ : Subst 𝒮 Γ Δ)
       -> ⟦subst⟧ (σ ↓ˢ k) ∘ ⟦ Δ ˢ⟧ ≈ ⟦ Γ ˢ⟧ ∘ ⟦subst⟧ σ
    ⟦↓ˢ⟧′ {Γ} {Δ} σ {n} {a} rewrite ⟦ˢ⟧-factor Δ {n} {a}
                                | □-≡ n n (⟦↓ˢ⟧ σ {n} {a}) n
                                | ⟦ˢ⟧-factor Γ {n} {(⟦subst⟧ σ n a)} = refl

    -- Denotation of stabilisation idempotence
    ⟦ˢˢ⟧ : ∀ Γ -> F-□.fmap (⟦subst⟧ (Γ ˢˢₛ k)) ∘ ⟦ Γ ˢ ˢ⟧□ ∘ ⟦ Γ ˢ⟧ ≈ ⟦ Γ ˢ⟧□
    ⟦ˢˢ⟧ ∙ = refl
    ⟦ˢˢ⟧ (Γ ,, B now) = ⟦ˢˢ⟧ Γ
    ⟦ˢˢ⟧ (Γ ,, B always) {n} {⟦Γˢ⟧ , □⟦B⟧} = ext lemma
        where
        lemma : ∀ l → (F-□.fmap (⟦subst⟧ ((Γ ,, B always) ˢˢₛ k))
                        ∘ ⟦ (Γ ,, B always) ˢ ˢ⟧□
                        ∘ ⟦ Γ ,, B always ˢ⟧) n (⟦Γˢ⟧ , □⟦B⟧) l
                    ≡ (⟦ Γ ˢ⟧□ n ⟦Γˢ⟧ l , □⟦B⟧)
        lemma l rewrite ⟦𝓋⟧ (B always) (Γ ˢ ˢ) {l} {⟦ Γ ˢ ˢ⟧□ n (⟦ Γ ˢ⟧ n ⟦Γˢ⟧) l , □⟦B⟧}
                      | ⟦⁺⟧ (B always) (Γ ˢˢₛ k) {l} {(⟦ Γ ˢ ˢ⟧□ n (⟦ Γ ˢ⟧ n ⟦Γˢ⟧) l , □⟦B⟧)}
                      | □-≡ n l (⟦ˢˢ⟧ Γ {n} {⟦Γˢ⟧}) l = refl

    -- Denotation of identity substitution
    ⟦idₛ⟧ : ∀ {Γ} -> ⟦subst⟧ (idₛ {Γ} k) ≈ id
    ⟦idₛ⟧ {∙} = refl
    ⟦idₛ⟧ {Γ ,, A} {n} {⟦Γ⟧ , ⟦A⟧}
        rewrite ⟦⁺⟧ A {Γ} (idₛ k) {n} {⟦Γ⟧ , ⟦A⟧}
              | ⟦idₛ⟧ {Γ} {n} {⟦Γ⟧}
              | ⟦𝓋⟧ A Γ {n} {⟦Γ⟧ , ⟦A⟧} = refl


    -- | Other lemmas

    -- Substitution by the Γ ˢ ⊆ Γ subcontext substitution is the same as
    -- stabilising the context
    ⟦subst⟧-Γˢ⊆Γ : ∀ Γ -> ⟦subst⟧ (Γˢ⊆Γ Γ ⊆ₛ k) ≈ ⟦ Γ ˢ⟧
    ⟦subst⟧-Γˢ⊆Γ ∙ = refl
    ⟦subst⟧-Γˢ⊆Γ (Γ ,, A now) {n} {⟦Γ⟧ , ⟦A⟧}
        rewrite ⟦⁺⟧ (A now) (Γˢ⊆Γ Γ ⊆ₛ k) {n} {⟦Γ⟧ , ⟦A⟧} = ⟦subst⟧-Γˢ⊆Γ Γ
    ⟦subst⟧-Γˢ⊆Γ (Γ ,, A always) {n} {⟦Γ⟧ , ⟦A⟧}
        rewrite ⟦↑⟧ (A always) (Γˢ⊆Γ Γ ⊆ₛ k) {n} {⟦Γ⟧ , ⟦A⟧}
              | ⟦subst⟧-Γˢ⊆Γ Γ {n} {⟦Γ⟧} = refl

    -- Interpretation of substitution and selection can be commuted
    ⟦subst⟧-handle : ∀{Δ Γ A B C} -> (σ : Subst 𝒮 Γ Δ)
        -> {⟦C₁⟧ : ⟦ Γ ˢ ⟧ₓ ⊗   ⟦ A ⟧ₜ ⊗ ◇ ⟦ B ⟧ₜ ⇴ ◇ ⟦ C ⟧ₜ}
        -> {⟦C₂⟧ : ⟦ Γ ˢ ⟧ₓ ⊗ ◇ ⟦ A ⟧ₜ ⊗   ⟦ B ⟧ₜ ⇴ ◇ ⟦ C ⟧ₜ}
        -> {⟦C₃⟧ : ⟦ Γ ˢ ⟧ₓ ⊗   ⟦ A ⟧ₜ ⊗   ⟦ B ⟧ₜ ⇴ ◇ ⟦ C ⟧ₜ}
        -> (handle
            (⟦C₁⟧ ∘ (⟦subst⟧ (_↑_ {Event B now} (_↑_ {A now} (σ ↓ˢ k) k) k)))
            (⟦C₂⟧ ∘ (⟦subst⟧ (_↑_ {B now} (_↑_ {Event A now} (σ ↓ˢ k) k) k)))
            (⟦C₃⟧ ∘ (⟦subst⟧ (_↑_ {B now} (_↑_ {A now}       (σ ↓ˢ k) k) k))))
         ≈ handle ⟦C₁⟧ ⟦C₂⟧ ⟦C₃⟧ ∘ (⟦subst⟧ (σ ↓ˢ k) * id)
    ⟦subst⟧-handle {A = A} {B} σ {n = n} {⟦Δ⟧ , inj₁ (inj₁ (⟦A⟧ , ⟦◇B⟧))}
        rewrite ⟦↑⟧ (Event B now) (_↑_ {A now} (σ ↓ˢ k) k) {n} {(⟦Δ⟧ , ⟦A⟧) , ⟦◇B⟧}
              | ⟦↑⟧ (A now) (σ ↓ˢ k) {n} {⟦Δ⟧ , ⟦A⟧} = refl
    ⟦subst⟧-handle {A = A} {B} σ {n = n} {⟦Δ⟧ , inj₁ (inj₂ (⟦B⟧ , ⟦◇A⟧))}
        rewrite ⟦↑⟧ (B now) (_↑_ {Event A now} (σ ↓ˢ k) k) {n} {(⟦Δ⟧ , ⟦B⟧) , ⟦◇A⟧}
              | ⟦↑⟧ (Event A now) (σ ↓ˢ k) {n} {⟦Δ⟧ , ⟦B⟧} = refl
    ⟦subst⟧-handle {A = A} {B} σ {n = n} {⟦Δ⟧ , inj₂ (⟦A⟧ , ⟦B⟧)}
        rewrite ⟦↑⟧ (B now) (_↑_ {A now} (σ ↓ˢ k) k) {n} {(⟦Δ⟧ , ⟦A⟧) , ⟦B⟧}
              | ⟦↑⟧ (A now) (σ ↓ˢ k) {n} {⟦Δ⟧ , ⟦A⟧} = refl
