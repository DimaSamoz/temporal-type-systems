
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

open import CategoryTheory.Categories using (Category ; ext)
open import CategoryTheory.NatTrans
open import CategoryTheory.Monad
open import CategoryTheory.Instances.Reactive renaming (top to ⊤)
open Category ℝeactive hiding (begin_ ; _∎)
open import TemporalOps.Diamond using (◇-select ; _>>=_ ; ◇_ ; M-◇ ; >>=-assoc)

open import Data.Sum
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as ≡
    using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; subst)

open ≡.≡-Reasoning

-- Denotation of variable kits
⟦𝒱ar⟧ : ⟦Kit⟧ 𝒱ar
⟦𝒱ar⟧ = record
    { ⟦_⟧ = ⟦_⟧-var
    ; ⟦𝓋⟧ = λ A Δ n ⟦Δ⟧ ⟦A⟧ → refl
    ; ⟦𝓉⟧ = ⟦𝓉⟧-var
    ; ⟦𝓌⟧ = λ B T n ⟦Δ⟧ ⟦B⟧ → refl
    ; ⟦𝒶⟧ = ⟦𝒶⟧-var
    }
    where
    open Kit 𝒱ar
    ⟦_⟧-var : ∀{A Γ} → Var Γ A → ⟦ Γ ⟧ₓ ⇴ ⟦ A ⟧ⱼ
    ⟦ top ⟧-var n (_ , ⟦A⟧) = ⟦A⟧
    ⟦ pop v ⟧-var n (⟦Γ⟧ , _) = ⟦ v ⟧-var n ⟦Γ⟧

    ⟦𝓉⟧-var : ∀{A Γ} → (x : Var Γ A)
          -> (n : ℕ) (⟦Γ⟧ : ⟦ Γ ⟧ₓ n)
          -> ⟦ 𝓉 x ⟧ₘ n ⟦Γ⟧ ≡ ⟦ x ⟧-var n ⟦Γ⟧
    ⟦𝓉⟧-var {A now} top n (⟦Γ⟧ , ⟦A⟧) = refl
    ⟦𝓉⟧-var {A always} top n (⟦Γ⟧ , ⟦A⟧) = refl
    ⟦𝓉⟧-var {A now} (pop x) n (⟦Γ⟧ , ⟦B⟧) = ⟦𝓉⟧-var x n ⟦Γ⟧
    ⟦𝓉⟧-var {A always} (pop x) n (⟦Γ⟧ , ⟦B⟧) = ⟦𝓉⟧-var x n ⟦Γ⟧

    ⟦𝒶⟧-var : ∀{A Γ} → (x : Var Γ (A always))
           -> (n l : ℕ) (⟦Γ⟧ : ⟦ Γ ⟧ₓ n)
           -> ⟦ 𝒶 x ⟧-var l (⟦ Γ ⟧ˢₓ n ⟦Γ⟧ l) ≡ ⟦ x ⟧-var n ⟦Γ⟧
    ⟦𝒶⟧-var top n l ⟦Γ⟧ = refl
    ⟦𝒶⟧-var (pop {B = B now} x) n l (⟦Γ⟧ , ⟦B⟧) = ⟦𝒶⟧-var x n l ⟦Γ⟧
    ⟦𝒶⟧-var (pop {B = B always} x) n l (⟦Γ⟧ , ⟦B⟧) = ⟦𝒶⟧-var x n l ⟦Γ⟧

-- Denotation of term kits
⟦𝒯erm⟧ : ⟦Kit⟧ 𝒯erm
⟦𝒯erm⟧ = record
    { ⟦_⟧ = ⟦_⟧ₘ
    ; ⟦𝓋⟧ = λ A Δ n ⟦Δ⟧ ⟦A⟧ → ⟦𝓉⟧ {A} {Δ ,, A} top n (⟦Δ⟧ , ⟦A⟧)
    ; ⟦𝓉⟧ = λ T n ⟦Δ⟧ → refl
    ; ⟦𝓌⟧ = ⟦𝓌⟧-term
    ; ⟦𝒶⟧ = ⟦𝒶⟧-term
    }
    where
    open Kit 𝒯erm
    open ⟦Kit⟧ ⟦𝒱ar⟧
    open K
    open ⟦K⟧

    ⟦𝓌⟧-term : ∀ B {Δ A} → (M : Term Δ A)
           -> (n : ℕ) (⟦Δ⟧ : ⟦ Δ ⟧ₓ n) (⟦B⟧ : ⟦ B ⟧ⱼ n)
           -> ⟦ 𝓌 {B} M ⟧ₘ n (⟦Δ⟧ , ⟦B⟧) ≡ ⟦ M ⟧ₘ n ⟦Δ⟧
    ⟦𝓌⟧-term B {Δ} M n ⟦Δ⟧ ⟦B⟧ =
        begin
            ⟦ 𝓌 M ⟧ₘ n (⟦Δ⟧ , ⟦B⟧)
        ≡⟨⟩
            ⟦ traverse 𝒱ar (idₛ 𝒱ar ⁺ 𝒱ar) M ⟧ₘ n (⟦Δ⟧ , ⟦B⟧)
        ≡⟨ traverse-sound ⟦𝒱ar⟧ (idₛ 𝒱ar ⁺ 𝒱ar) M n (⟦Δ⟧ , ⟦B⟧) ⟩
            ⟦ M ⟧ₘ n (⟦subst⟧ ⟦𝒱ar⟧ {Δ} ((_⁺_ {B} (idₛ 𝒱ar) 𝒱ar)) n (⟦Δ⟧ , ⟦B⟧))
        ≡⟨ cong (⟦ M ⟧ₘ n) (
            begin
                ⟦subst⟧ ⟦𝒱ar⟧ (idₛ 𝒱ar ⁺ 𝒱ar) n (⟦Δ⟧ , ⟦B⟧)
            ≡⟨ ⟦⁺⟧ ⟦𝒱ar⟧ B (idₛ 𝒱ar) n ⟦Δ⟧ ⟦B⟧ ⟩
                ⟦subst⟧ ⟦𝒱ar⟧ (idₛ 𝒱ar) n ⟦Δ⟧
            ≡⟨ ⟦idₛ⟧ ⟦𝒱ar⟧ n ⟦Δ⟧ ⟩
                ⟦Δ⟧
            ∎)
         ⟩
            ⟦ M ⟧ₘ n ⟦Δ⟧
        ∎

    postulate
        duh : ∀ {A : Set}{x y : A} -> x ≡ y

    ⟦𝒶⟧-term : ∀{A Δ} → (M : Term Δ (A always))
           -> (n l : ℕ) (⟦Δ⟧ : ⟦ Δ ⟧ₓ n)
           -> ⟦ 𝒶 M ⟧ₘ l (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ l) ≡ ⟦ M ⟧ₘ n ⟦Δ⟧
    ⟦𝒶⟧-term {A} {∙} (svar ()) n l ⊤.tt
    ⟦𝒶⟧-term {A} {∙} (stable M) n l ⊤.tt = refl
    ⟦𝒶⟧-term {A} {Δ ,, B now} (svar (pop x)) n l (⟦Δ⟧ , ⟦B⟧) = ⟦𝒶⟧-term (svar x) n l ⟦Δ⟧
    ⟦𝒶⟧-term {A} {Δ ,, B now} (stable M) n l (⟦Δ⟧ , ⟦B⟧) = ⟦𝒶⟧-term {A} {Δ} (stable M) n l ⟦Δ⟧
    ⟦𝒶⟧-term {Δ = Δ ,, B always} (svar {A = .B} top) n l (⟦Δ⟧ , ⟦B⟧) = refl
    ⟦𝒶⟧-term {Δ = Δ ,, B always} (svar {A = A} (pop x)) n l (⟦Δ⟧ , ⟦B⟧)
        rewrite ⟦𝓌⟧-term (B always) (𝒶 (svar x)) l (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ l) ⟦B⟧
              | ⟦𝒶⟧-term (svar x) n l ⟦Δ⟧ = refl
    ⟦𝒶⟧-term {A} {Δ ,, B always} (stable M) n l (⟦Δ⟧ , ⟦B⟧) = ext λ m →
        begin
            ⟦ 𝒶 (stable {Δ ,, B always} M) ⟧ₘ l (⟦ Δ ,, B always ⟧ˢₓ n (⟦Δ⟧ , ⟦B⟧) l) m
        ≡⟨⟩
            ⟦ subst (λ x → x ,, B always ⊢ A now) (sym (ˢ-idemp Δ)) M ⟧ₘ m (⟦ Δ ˢ ⟧ˢₓ l (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ l) m , ⟦B⟧)
        ≡⟨ duh ⟩
            ⟦ M ⟧ₘ m (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ m , ⟦B⟧)
        ≡⟨⟩
            ⟦ stable {Δ ,, B always} M ⟧ₘ n (⟦Δ⟧ , ⟦B⟧) m
        ∎
