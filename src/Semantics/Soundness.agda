
-- Soundness of term equality
module Semantics.Soundness where

open import Syntax.Types
open import Syntax.Context renaming (_,_ to _,,_)
open import Syntax.Terms
open import Syntax.Kit
open import Syntax.Traversal
open import Syntax.Equality

open import Semantics.Types
open import Semantics.Context
open import Semantics.Select
open import Semantics.Terms
open import Semantics.Kit
open import Semantics.Traversal

open import CategoryTheory.Categories using (Category ; ext)
open import CategoryTheory.BCCCs.Cartesian using (Product)
open import CategoryTheory.BCCCs
open import CategoryTheory.Instances.Reactive renaming (top to ⊤)
open Category ℝeactive hiding (begin_ ; _∎)
open import TemporalOps.Diamond using (◇-select ; _>>=_ ; ◇_)

open import Data.Sum
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as ≡
    using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; subst)

open ≡.≡-Reasoning

open ⟦Kit⟧ ⟦𝒯erm⟧
open Kit 𝒯erm
open ⟦K⟧ ⟦𝒯erm⟧
open K 𝒯erm

-- Soundness of term equality: equal terms have equal denotations
sound : ∀{A Γ} {M₁ M₂ : Γ ⊢ A}
         -- -> (n : ℕ) (⟦Γ⟧ : ⟦ Γ ⟧ₓ n)
         -> Γ ⊢ M₁ ≡ M₂ ∷ A
         -> ⟦ M₁ ⟧ₘ ≈ ⟦ M₂ ⟧ₘ
sound (refl M) = refl
sound (Eq.sym eq) = ≡.sym (sound eq)
sound (Eq.trans eq₁ eq₂) = ≡.trans (sound eq₁) (sound eq₂)

sound (β-lam N M) {n} {⟦Γ⟧} rewrite subst-sound M N {n} {⟦Γ⟧} = refl
sound (β-fst M N) = refl
sound (β-snd M N) = refl
sound (β-inl M N₁ N₂) {n} {⟦Γ⟧} rewrite subst-sound M N₁ {n} {⟦Γ⟧} = refl
sound (β-inr M N₁ N₂) {n} {⟦Γ⟧} rewrite subst-sound M N₂ {n} {⟦Γ⟧} = refl
sound (β-sig N M) {n} {⟦Γ⟧} rewrite subst-sound M N {n} {⟦Γ⟧} = refl

sound (η-lam {A} M) {n} {⟦Γ⟧} = ext λ ⟦A⟧ →
                    cong (λ x → x ⟦A⟧) (≡.sym (⟦𝓌⟧ (A now) M n ⟦Γ⟧ ⟦A⟧))
sound (η-pair M) {n} {⟦Γ⟧} with ⟦ M ⟧ₘ n ⟦Γ⟧
sound (η-pair M) {n} {⟦Γ⟧} | _ , _ = refl
sound (η-unit M) = refl
sound (η-sum M) {n} {⟦Γ⟧} with ⟦ M ⟧ₘ n ⟦Γ⟧
sound (η-sum M) {n} {a} | inj₁ _ = refl
sound (η-sum M) {n} {a} | inj₂ _ = refl
sound (η-sig M) = refl

sound (cong-pair eq₁ eq₂) {n} {a} rewrite sound eq₁ {n} {a}
                                        | sound eq₂ {n} {a} = refl
sound (cong-fst eq) {n} {a} rewrite sound eq {n} {a} = refl
sound (cong-snd eq) {n} {a} rewrite sound eq {n} {a} = refl
sound (cong-lam eq) {n} {a} = ext λ ⟦A⟧ → sound eq
sound (cong-app eq₁ eq₂) {n} {a} rewrite sound eq₁ {n} {a}
                                       | sound eq₂ {n} {a} = refl
sound (cong-inl eq) {n} {a} rewrite sound eq {n} {a} = refl
sound (cong-inr eq) {n} {a} rewrite sound eq {n} {a} = refl
sound (cong-case eq N₁ N₂) {n} {a} rewrite sound eq {n} {a} = refl
sound (cong-sig eq) {n} {a} rewrite sound eq {n} {a} = refl
sound (cong-letSig eq N) {n} {a} rewrite sound eq {n} {a} = refl
sound (cong-sample eq) {n} {a} rewrite sound eq {n} {a} = refl
sound (cong-stable eq) = ext λ k → sound eq

-- Soundness of computational term equality: equal terms have equal denotations
sound′ : ∀{A Γ} {M₁ M₂ : Γ ⊨ A}
         -- -> (n : ℕ) (⟦Γ⟧ : ⟦ Γ ⟧ₓ n)
         -> Γ ⊨ M₁ ≡ M₂ ∷ A
         -> ⟦ M₁ ⟧ᵐ ≈ ⟦ M₂ ⟧ᵐ
sound′ (refl M) = refl
sound′ (Eq′.sym eq) = ≡.sym (sound′ eq)
sound′ (Eq′.trans eq₁ eq₂) = ≡.trans (sound′ eq₁) (sound′ eq₂)
sound′ (β-sig′ C M) {n} {⟦Γ⟧} rewrite subst-sound′ M C {n} {⟦Γ⟧} = refl
sound′ (η-sig′ M) = refl
sound′ (cong-pure′ eq) {n} {⟦Γ⟧} rewrite sound eq {n} {⟦Γ⟧} = refl
sound′ (cong-letSig′ eq B) {n} {⟦Γ⟧} rewrite sound eq {n} {⟦Γ⟧} = refl
