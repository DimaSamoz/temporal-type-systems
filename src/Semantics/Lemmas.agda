
-- Semantic versions of structural lemmas
module Semantics.Lemmas where

open import Syntax.Types
open import Syntax.Context hiding (_,_)
open import Syntax.Lemmas
open import Syntax.Terms
open import Syntax.Substitution

open import Semantics.Types
open import Semantics.Context
open import Semantics.Select
open import Semantics.Terms

open import CategoryTheory.Categories using (Category ; ext)
open import CategoryTheory.Instances.Reactive
open Category ℝeactive
open import TemporalOps.Diamond using (◇-select ; _>>=_ ; ◇_)

open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality as ≡
    using (_≡_ ; refl ; sym ; trans ; cong)
open ≡.≡-Reasoning


-- | Semantic weakening lemma: the denotation of a term M weakened by an OPE s
-- is the same as the denotation of M composed with the denotation of s

mutual
    -- Weakening for pure terms
    ⟦weaken⟧ : ∀{Γ Δ A} -> (s : Γ ⊆ Δ) -> (M : Γ ⊢ A)
            -> ∀ (n : ℕ) (⟦Δ⟧ : ⟦ Δ ⟧ₓ n)
            -> ⟦ weaken s M ⟧ₘ n ⟦Δ⟧ ≡ ⟦ M ⟧ₘ n (⟦ s ⟧⊆ n ⟦Δ⟧)
    ⟦weaken⟧ refl (var x) n ⟦Δ⟧ = refl
    ⟦weaken⟧ (keep s) (var _∈_.top) n (⟦Δ⟧ , ⟦A⟧) = refl
    ⟦weaken⟧ (keep s) (var (pop x)) n (⟦Δ⟧ , ⟦A⟧) = ⟦weaken⟧ s (var x) n ⟦Δ⟧
    ⟦weaken⟧ (drop s) (var x) n (⟦Δ⟧ , ⟦A⟧) = ⟦weaken⟧ s (var x) n ⟦Δ⟧
    ⟦weaken⟧ s (lam M) n ⟦Δ⟧ = ext λ ⟦A⟧ → ⟦weaken⟧ (keep s) M n (⟦Δ⟧ , ⟦A⟧)
    ⟦weaken⟧ s (M $ N) n ⟦Δ⟧ rewrite ⟦weaken⟧ s M n ⟦Δ⟧
                                    | ⟦weaken⟧ s N n ⟦Δ⟧ = refl
    ⟦weaken⟧ s unit n ⟦Δ⟧ = refl
    ⟦weaken⟧ s [ M ,, N ] n ⟦Δ⟧ rewrite ⟦weaken⟧ s M n ⟦Δ⟧
                                       | ⟦weaken⟧ s N n ⟦Δ⟧ = refl
    ⟦weaken⟧ s (fst M) n ⟦Δ⟧ rewrite ⟦weaken⟧ s M n ⟦Δ⟧ = refl
    ⟦weaken⟧ s (snd M) n ⟦Δ⟧ rewrite ⟦weaken⟧ s M n ⟦Δ⟧ = refl
    ⟦weaken⟧ s (inl M) n ⟦Δ⟧ rewrite ⟦weaken⟧ s M n ⟦Δ⟧ = refl
    ⟦weaken⟧ s (inr M) n ⟦Δ⟧ rewrite ⟦weaken⟧ s M n ⟦Δ⟧ = refl
    ⟦weaken⟧ s (case M inl↦ M₁ ||inr↦ M₂) n ⟦Δ⟧
        rewrite ⟦weaken⟧ s M n ⟦Δ⟧ with ⟦ M ⟧ₘ n (⟦ s ⟧⊆ n ⟦Δ⟧)
    ⟦weaken⟧ s (case M inl↦ M₁ ||inr↦ M₂) n ⟦Δ⟧ | inj₁ ⟦A⟧ = ⟦weaken⟧ (keep s) M₁ n (⟦Δ⟧ , ⟦A⟧)
    ⟦weaken⟧ s (case M inl↦ M₁ ||inr↦ M₂) n ⟦Δ⟧ | inj₂ ⟦B⟧ = ⟦weaken⟧ (keep s) M₂ n (⟦Δ⟧ , ⟦B⟧)
    ⟦weaken⟧ refl (svar x) n ⟦Δ⟧ = refl
    ⟦weaken⟧ (keep s) (svar _∈_.top) n ⟦Δ⟧ = refl
    ⟦weaken⟧ (keep s) (svar (pop x)) n ⟦Δ⟧ = ⟦weaken⟧ s (svar x) n (proj₁ ⟦Δ⟧)
    ⟦weaken⟧ (drop s) (svar x) n ⟦Δ⟧ = ⟦weaken⟧ s (svar x) n (proj₁ ⟦Δ⟧)
    ⟦weaken⟧ s (present M) n ⟦Δ⟧ rewrite ⟦weaken⟧ s M n ⟦Δ⟧ = refl
    ⟦weaken⟧ refl (stable {Γ} M) n ⟦Δ⟧ = ext λ k → ⟦weaken⟧ refl M k (⟦ Γ ⟧ˢₓ n ⟦Δ⟧ k)
    ⟦weaken⟧ (keep {Γ} {Δ} {A now} s) (stable M) n (⟦Δ⟧ , ⟦A⟧) = ext λ k →
            ≡.≡-Reasoning.begin
                ⟦ weaken (ˢ-⊆-monotone s) M ⟧ₘ k (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ k)
            ≡⟨ ⟦weaken⟧ (ˢ-⊆-monotone s) M k (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ k) ⟩
                ⟦ M ⟧ₘ k (⟦ ˢ-⊆-monotone s ⟧⊆ k (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ k))
            ≡⟨ cong (λ x → ⟦ M ⟧ₘ k x) (⟦⟧ˢₓ-⟦⟧⊆-comm n k s ⟦Δ⟧) ⟩
                ⟦ M ⟧ₘ k (⟦ Γ ⟧ˢₓ n (⟦ s ⟧⊆ n ⟦Δ⟧) k)
            ≡.≡-Reasoning.∎
    ⟦weaken⟧ (keep {Γ} {Δ} {A always} s) (stable M) n (⟦Δ⟧ , ⟦A⟧) = ext λ k →
            ≡.≡-Reasoning.begin
                ⟦ weaken (keep (ˢ-⊆-monotone s)) M ⟧ₘ k (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ k , ⟦A⟧)
            ≡⟨ ⟦weaken⟧ (keep (ˢ-⊆-monotone s)) M k (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ k , ⟦A⟧) ⟩
                ⟦ M ⟧ₘ k (⟦ ˢ-⊆-monotone s ⟧⊆ k (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ k) , ⟦A⟧)
            ≡⟨ cong (λ x → ⟦ M ⟧ₘ k (x , ⟦A⟧)) (⟦⟧ˢₓ-⟦⟧⊆-comm n k s ⟦Δ⟧) ⟩
                ⟦ M ⟧ₘ k (⟦ Γ ⟧ˢₓ n (⟦ s ⟧⊆ n ⟦Δ⟧) k , ⟦A⟧)
            ≡.≡-Reasoning.∎
    ⟦weaken⟧ (drop {Γ} {Δ} {A now} s) (stable M) n (⟦Δ⟧ , ⟦A⟧) = ext λ k →
            trans (⟦weaken⟧ (ˢ-⊆-monotone s) M k (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ k))
                  (cong (λ x → ⟦ M ⟧ₘ k x) (⟦⟧ˢₓ-⟦⟧⊆-comm n k s ⟦Δ⟧))
    ⟦weaken⟧ (drop {Γ} {Δ} {A always} s) (stable M) n (⟦Δ⟧ , ⟦A⟧) = ext λ k →
            trans (⟦weaken⟧ (drop (ˢ-⊆-monotone s)) M k (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ k , ⟦A⟧))
                  (cong (λ x → ⟦ M ⟧ₘ k x) (⟦⟧ˢₓ-⟦⟧⊆-comm n k s ⟦Δ⟧))
    ⟦weaken⟧ s (sig M) n ⟦Δ⟧ = ⟦weaken⟧ s M n ⟦Δ⟧
    ⟦weaken⟧ s (letSig M In N) n ⟦Δ⟧ rewrite ⟦weaken⟧ s M n ⟦Δ⟧ =
        ⟦weaken⟧ (keep s) N n (⟦Δ⟧ , ⟦ M ⟧ₘ n (⟦ s ⟧⊆ n ⟦Δ⟧))
    ⟦weaken⟧ s (event E) n ⟦Δ⟧ rewrite ⟦weaken′⟧ s E n ⟦Δ⟧ = refl

    -- Weakening for computational terms
    ⟦weaken′⟧ : ∀{Γ Δ A} -> (s : Γ ⊆ Δ) -> (M : Γ ⊨ A)
            -> ∀ (n : ℕ) (⟦Δ⟧ : ⟦ Δ ⟧ₓ n)
            -> ⟦ weaken′ s M ⟧ᵐ n ⟦Δ⟧ ≡ ⟦ M ⟧ᵐ n (⟦ s ⟧⊆ n ⟦Δ⟧)
    ⟦weaken′⟧ s (pure M) n ⟦Δ⟧ rewrite ⟦weaken⟧ s M n ⟦Δ⟧ = refl
    ⟦weaken′⟧ s (letSig M InC C) n ⟦Δ⟧ rewrite ⟦weaken⟧ s M n ⟦Δ⟧ =
        ⟦weaken′⟧ (keep s) C n (⟦Δ⟧ , ⟦ M ⟧ₘ n (⟦ s ⟧⊆ n ⟦Δ⟧) n)
    ⟦weaken′⟧ {Γ} {Δ} s (letEvt E In C) n ⟦Δ⟧ =
        ≡.≡-Reasoning.begin
            ⟦ weaken′ s (letEvt E In C) ⟧ᵐ n ⟦Δ⟧
        ≡⟨⟩
            ⟦ letEvt (weaken s E) In (weaken′ (keep (ˢ-⊆-monotone s)) C) ⟧ᵐ n ⟦Δ⟧
        ≡⟨⟩
            ⟦ weaken s E ⟧ₘ n ⟦Δ⟧ >>= (λ k ⟦A⟧ → ⟦ weaken′ (keep (ˢ-⊆-monotone s)) C ⟧ᵐ k (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ k , ⟦A⟧))
        ≡⟨ cong (λ x → x >>= _) (⟦weaken⟧ s E n ⟦Δ⟧) ⟩
            ⟦ E ⟧ₘ n (⟦ s ⟧⊆ n ⟦Δ⟧) >>= (λ k ⟦A⟧ → ⟦ weaken′ (keep (ˢ-⊆-monotone s)) C ⟧ᵐ k (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ k , ⟦A⟧))
        ≡⟨ cong (λ x → ⟦ E ⟧ₘ n (⟦ s ⟧⊆ n ⟦Δ⟧) >>= x) (ext λ k → ext λ ⟦A⟧ →
            (≡.≡-Reasoning.begin
                ⟦ weaken′ (keep (ˢ-⊆-monotone s)) C ⟧ᵐ k (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ k , ⟦A⟧)
            ≡⟨ ⟦weaken′⟧ (keep (ˢ-⊆-monotone s)) C k (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ k , ⟦A⟧) ⟩
                ⟦ C ⟧ᵐ k (⟦ ˢ-⊆-monotone s ⟧⊆ k (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ k) , ⟦A⟧)
            ≡⟨ cong (λ x → ⟦ C ⟧ᵐ k (x , ⟦A⟧)) (⟦⟧ˢₓ-⟦⟧⊆-comm n k s ⟦Δ⟧) ⟩
                ⟦ C ⟧ᵐ k (⟦ Γ ⟧ˢₓ n (⟦ s ⟧⊆ n ⟦Δ⟧) k , ⟦A⟧)
            ≡.≡-Reasoning.∎)
            )
         ⟩
            ⟦ E ⟧ₘ n (⟦ s ⟧⊆ n ⟦Δ⟧) >>= (λ k ⟦A⟧ → ⟦ C ⟧ᵐ k (⟦ Γ ⟧ˢₓ n (⟦ s ⟧⊆ n ⟦Δ⟧) k , ⟦A⟧))
        ≡⟨⟩
            ⟦ letEvt E In C ⟧ᵐ n (⟦ s ⟧⊆ n ⟦Δ⟧)
        ≡.≡-Reasoning.∎
    ⟦weaken′⟧ {Γ} {Δ} s (select_↦_||_↦_||both↦_ {A = A} {B} {C} E₁ C₁ E₂ C₂ C₃) n ⟦Δ⟧ =
        ≡.≡-Reasoning.begin
            ⟦ weaken′ s (select E₁ ↦ C₁ || E₂ ↦ C₂ ||both↦ C₃) ⟧ᵐ n ⟦Δ⟧
        ≡⟨⟩
            ⟦ select weaken s E₁ ↦ weaken′ (keep (keep (ˢ-⊆-monotone s))) C₁
                  || weaken s E₂ ↦ weaken′ (keep (keep (ˢ-⊆-monotone s))) C₂
                  ||both↦ weaken′ (keep (keep (ˢ-⊆-monotone s))) C₃ ⟧ᵐ n ⟦Δ⟧
        ≡⟨⟩
            ◇-select n (⟦ weaken s E₁ ⟧ₘ n ⟦Δ⟧ , ⟦ weaken s E₂ ⟧ₘ n ⟦Δ⟧)
            >>= ⟦select⟧ Δ A B C n ⟦Δ⟧ ⟦ weaken′ (keep (keep (ˢ-⊆-monotone s))) C₁ ⟧ᵐ
                                      ⟦ weaken′ (keep (keep (ˢ-⊆-monotone s))) C₂ ⟧ᵐ
                                      ⟦ weaken′ (keep (keep (ˢ-⊆-monotone s))) C₃ ⟧ᵐ
        ≡⟨ cong (λ x → ◇-select n (⟦ weaken s E₁ ⟧ₘ n ⟦Δ⟧ , ⟦ weaken s E₂ ⟧ₘ n ⟦Δ⟧) >>= x)
            (ext λ k → ext λ c →
            (≡.≡-Reasoning.begin
                ⟦select⟧ Δ A B C n ⟦Δ⟧
                    ⟦ weaken′ (keep (keep (ˢ-⊆-monotone s))) C₁ ⟧ᵐ
                    ⟦ weaken′ (keep (keep (ˢ-⊆-monotone s))) C₂ ⟧ᵐ
                    ⟦ weaken′ (keep (keep (ˢ-⊆-monotone s))) C₃ ⟧ᵐ k c
            ≡⟨ ind-hyp k c ⟩
                ⟦select⟧ Δ A B C n ⟦Δ⟧
                      (⟦ C₁ ⟧ᵐ ∘ ⟦ keep {A = A now} (keep {A = (Event B) now} (ˢ-⊆-monotone s)) ⟧⊆)
                      (⟦ C₂ ⟧ᵐ ∘ ⟦ keep {A = B now} (keep {A = (Event A) now} (ˢ-⊆-monotone s)) ⟧⊆)
                      (⟦ C₃ ⟧ᵐ ∘ ⟦ keep {A = B now} (keep {A = A now} (ˢ-⊆-monotone s)) ⟧⊆) k c
            ≡⟨ ⟦select⟧-⟦⟧⊆-comm A B n k c s ⟦Δ⟧ ⟩
                ⟦select⟧ Γ A B C n (⟦ s ⟧⊆ n ⟦Δ⟧) ⟦ C₁ ⟧ᵐ ⟦ C₂ ⟧ᵐ ⟦ C₃ ⟧ᵐ k c
            ≡.≡-Reasoning.∎))

         ⟩
            ◇-select n (⟦ weaken s E₁ ⟧ₘ n ⟦Δ⟧ , ⟦ weaken s E₂ ⟧ₘ n ⟦Δ⟧)
            >>= ⟦select⟧ Γ A B C n (⟦ s ⟧⊆ n ⟦Δ⟧) ⟦ C₁ ⟧ᵐ ⟦ C₂ ⟧ᵐ ⟦ C₃ ⟧ᵐ
        ≡⟨ ≡.cong₂ (λ x y → ◇-select n (x , y) >>= _) (⟦weaken⟧ s E₁ n ⟦Δ⟧) (⟦weaken⟧ s E₂ n ⟦Δ⟧) ⟩
            ◇-select n (⟦ E₁ ⟧ₘ n (⟦ s ⟧⊆ n ⟦Δ⟧) , ⟦ E₂ ⟧ₘ n (⟦ s ⟧⊆ n ⟦Δ⟧))
            >>= ⟦select⟧ Γ A B C n (⟦ s ⟧⊆ n ⟦Δ⟧) ⟦ C₁ ⟧ᵐ ⟦ C₂ ⟧ᵐ ⟦ C₃ ⟧ᵐ
        ≡⟨⟩
            ⟦ select E₁ ↦ C₁ || E₂ ↦ C₂ ||both↦ C₃ ⟧ᵐ n (⟦ s ⟧⊆ n ⟦Δ⟧)
        ≡.≡-Reasoning.∎
        where
        ind-hyp : ∀ k c
               -> ⟦select⟧ Δ A B C n ⟦Δ⟧
                    ⟦ weaken′ (keep (keep (ˢ-⊆-monotone s))) C₁ ⟧ᵐ
                    ⟦ weaken′ (keep (keep (ˢ-⊆-monotone s))) C₂ ⟧ᵐ
                    ⟦ weaken′ (keep (keep (ˢ-⊆-monotone s))) C₃ ⟧ᵐ k c
                ≡ ⟦select⟧ Δ A B C n ⟦Δ⟧
                    (⟦ C₁ ⟧ᵐ ∘ ⟦ keep {A = A now} (keep {A = (Event B) now} (ˢ-⊆-monotone s)) ⟧⊆)
                    (⟦ C₂ ⟧ᵐ ∘ ⟦ keep {A = B now} (keep {A = (Event A) now} (ˢ-⊆-monotone s)) ⟧⊆)
                    (⟦ C₃ ⟧ᵐ ∘ ⟦ keep {A = B now} (keep {A = A now} (ˢ-⊆-monotone s)) ⟧⊆) k c
        ind-hyp k c rewrite ext (λ n -> ext (λ ⟦Δ⟧ -> ⟦weaken′⟧ (keep (keep (ˢ-⊆-monotone s))) C₁ n ⟦Δ⟧))
                      | ext (λ n -> ext (λ ⟦Δ⟧ -> ⟦weaken′⟧ (keep (keep (ˢ-⊆-monotone s))) C₂ n ⟦Δ⟧))
                      | ext (λ n -> ext (λ ⟦Δ⟧ -> ⟦weaken′⟧ (keep (keep (ˢ-⊆-monotone s))) C₃ n ⟦Δ⟧)) = refl
