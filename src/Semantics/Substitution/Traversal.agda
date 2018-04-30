
-- Semantics of syntactic traversal and substitution
module Semantics.Substitution.Traversal where

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

open import CategoryTheory.Categories using (Category ; ext)
open import CategoryTheory.NatTrans
open import CategoryTheory.Monad
open import CategoryTheory.Instances.Reactive renaming (top to ⊤)
open import TemporalOps.Diamond using (◇-select ; _>>=_ ; ◇_ ; M-◇ ; >>=-assoc)

open import Data.Sum
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as ≡
    using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; subst)

open ≡.≡-Reasoning


module _ {𝒮} {k : Kit 𝒮} (⟦k⟧ : ⟦Kit⟧ k) where
    open ⟦Kit⟧ ⟦k⟧
    open Kit k
    open ⟦K⟧ ⟦k⟧
    open K k

    -- Soundness of syntactic traversal:
    -- Denotation of a term M traversed with substitution σ is
    -- the same as the denotation of σ followed by the denotation of M
    mutual
        traverse-sound : ∀{Γ Δ A} (σ : Subst 𝒮 Γ Δ) (M : Γ ⊢ A)
                      -> (n : ℕ) -> (⟦Δ⟧ : ⟦ Δ ⟧ₓ n)
                      -> ⟦ traverse σ M ⟧ₘ n ⟦Δ⟧ ≡ ⟦ M ⟧ₘ n (⟦subst⟧ σ n ⟦Δ⟧)
        traverse-sound ● (var ()) n ⟦Δ⟧
        traverse-sound (σ ▸ T) (var top) n ⟦Δ⟧ = ⟦𝓉⟧ T n ⟦Δ⟧
        traverse-sound (σ ▸ T) (var (pop x)) n ⟦Δ⟧ = traverse-sound σ (var x) n ⟦Δ⟧
        traverse-sound σ (lam {A = A} M) n ⟦Δ⟧ = ext λ ⟦A⟧ →
            begin
                ⟦ traverse (σ ↑ k) M ⟧ₘ n (⟦Δ⟧ , ⟦A⟧)
            ≡⟨ traverse-sound (σ ↑ k) M n (⟦Δ⟧ , ⟦A⟧) ⟩
                ⟦ M ⟧ₘ n (⟦subst⟧ (_↑_ {A now} σ k) n (⟦Δ⟧ , ⟦A⟧))
            ≡⟨ cong (λ x → ⟦ M ⟧ₘ n x) (⟦↑⟧ (A now) σ n ⟦Δ⟧ ⟦A⟧) ⟩
                ⟦ M ⟧ₘ n (⟦subst⟧ σ n ⟦Δ⟧ , ⟦A⟧)
            ∎
        traverse-sound σ (M $ N) n ⟦Δ⟧ rewrite traverse-sound σ M n ⟦Δ⟧
                                             | traverse-sound σ N n ⟦Δ⟧ = refl
        traverse-sound σ unit n ⟦Δ⟧ = refl
        traverse-sound σ [ M ,, N ] n ⟦Δ⟧
                                   rewrite traverse-sound σ M n ⟦Δ⟧
                                         | traverse-sound σ N n ⟦Δ⟧ = refl
        traverse-sound σ (fst M) n ⟦Δ⟧ rewrite traverse-sound σ M n ⟦Δ⟧ = refl
        traverse-sound σ (snd M) n ⟦Δ⟧ rewrite traverse-sound σ M n ⟦Δ⟧ = refl
        traverse-sound σ (inl M) n ⟦Δ⟧ rewrite traverse-sound σ M n ⟦Δ⟧ = refl
        traverse-sound σ (inr M) n ⟦Δ⟧ rewrite traverse-sound σ M n ⟦Δ⟧ = refl
        traverse-sound σ (case M inl↦ N₁ ||inr↦ N₂) n ⟦Δ⟧
            rewrite traverse-sound σ M n ⟦Δ⟧ with ⟦ M ⟧ₘ n (⟦subst⟧ σ n ⟦Δ⟧)
        traverse-sound σ (case_inl↦_||inr↦_ {A = A} M N₁ N₂) n ⟦Δ⟧ | inj₁ ⟦A⟧
            rewrite traverse-sound (σ ↑ k) N₁ n (⟦Δ⟧ , ⟦A⟧)
                  | ⟦↑⟧ (A now) σ n ⟦Δ⟧ ⟦A⟧ = refl
        traverse-sound σ (case_inl↦_||inr↦_ {B = B} M N₁ N₂) n ⟦Δ⟧ | inj₂ ⟦B⟧
            rewrite traverse-sound (σ ↑ k) N₂ n (⟦Δ⟧ , ⟦B⟧)
                  | ⟦↑⟧ (B now) σ n ⟦Δ⟧ ⟦B⟧ = refl
        traverse-sound ● (svar ()) n ⟦Δ⟧
        traverse-sound (σ ▸ T) (svar top) n ⟦Δ⟧ = ⟦𝓉⟧ T n ⟦Δ⟧
        traverse-sound (σ ▸ T) (svar (pop x)) n ⟦Δ⟧ = traverse-sound σ (svar x) n ⟦Δ⟧
        traverse-sound σ (sample M) n ⟦Δ⟧ rewrite traverse-sound σ M n ⟦Δ⟧ = refl
        traverse-sound {Γ} {Δ} {A} σ (stable M) n ⟦Δ⟧ = ext λ l ->
            begin
                ⟦ traverse {Γ} {Δ} {A} σ (stable M) ⟧ₘ n ⟦Δ⟧ l
            ≡⟨ traverse-sound (σ ↓ˢ k) M l (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ l) ⟩
                ⟦ M ⟧ₘ l (⟦subst⟧ (σ ↓ˢ k) l (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ l))
            ≡⟨ cong (⟦ M ⟧ₘ l) (⟦subst⟧-⟦⟧ˢₓ σ n l ⟦Δ⟧) ⟩
                ⟦ M ⟧ₘ l (⟦ Γ ⟧ˢₓ n (⟦subst⟧ σ n ⟦Δ⟧) l)
            ≡⟨⟩
                ⟦ stable {Γ} M ⟧ₘ n (⟦subst⟧ σ n ⟦Δ⟧) l
            ∎
        traverse-sound σ (sig M) n ⟦Δ⟧ rewrite traverse-sound σ M n ⟦Δ⟧ = refl
        traverse-sound σ (letSig_In_ {A = A} M N) n ⟦Δ⟧
            rewrite traverse-sound σ M n ⟦Δ⟧
                  | traverse-sound (σ ↑ k) N n (⟦Δ⟧ , ⟦ M ⟧ₘ n (⟦subst⟧ σ n ⟦Δ⟧))
                  | ⟦↑⟧ (A always) σ n ⟦Δ⟧ (⟦ M ⟧ₘ n (⟦subst⟧ σ n ⟦Δ⟧)) = refl
        traverse-sound σ (event E) n ⟦Δ⟧ rewrite traverse′-sound σ E n ⟦Δ⟧ = refl

        traverse′-sound : ∀{Γ Δ A} -> (σ : Subst 𝒮 Γ Δ) -> (C : Γ ⊨ A)
                  -> (n : ℕ) -> (⟦Δ⟧ : ⟦ Δ ⟧ₓ n)
                  -> ⟦ traverse′ σ C ⟧ᵐ n ⟦Δ⟧ ≡ ⟦ C ⟧ᵐ n (⟦subst⟧ σ n ⟦Δ⟧)
        traverse′-sound σ (pure M) n ⟦Δ⟧ rewrite traverse-sound σ M n ⟦Δ⟧ = refl
        traverse′-sound σ (letSig_InC_ {A = A} S C) n ⟦Δ⟧
            rewrite traverse-sound σ S n ⟦Δ⟧
                  | traverse′-sound (σ ↑ k) C n (⟦Δ⟧ , ⟦ S ⟧ₘ n (⟦subst⟧ σ n ⟦Δ⟧))
                  | ⟦↑⟧ (A always) σ n ⟦Δ⟧ (⟦ S ⟧ₘ n (⟦subst⟧ σ n ⟦Δ⟧)) = refl
        traverse′-sound {Γ} {Δ} σ (letEvt_In_ {A = A} E C) n ⟦Δ⟧ =
            begin
                ⟦ traverse′ σ (letEvt E In C) ⟧ᵐ n ⟦Δ⟧
            ≡⟨⟩
                ⟦ letEvt (traverse σ E) In (traverse′ (σ ↓ˢ k ↑ k) C) ⟧ᵐ n ⟦Δ⟧
            ≡⟨⟩
                ⟦ traverse σ E ⟧ₘ n ⟦Δ⟧ >>= (λ l ⟦A⟧ → ⟦ traverse′ (σ ↓ˢ k ↑ k) C ⟧ᵐ l (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ l , ⟦A⟧))
            ≡⟨ cong (λ x → x >>= _) (traverse-sound σ E n ⟦Δ⟧) ⟩
                ⟦ E ⟧ₘ n (⟦subst⟧ σ n ⟦Δ⟧) >>= (λ l ⟦A⟧ → ⟦ traverse′ (σ ↓ˢ k ↑ k) C ⟧ᵐ l (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ l , ⟦A⟧))
            ≡⟨ cong (λ x → ⟦ E ⟧ₘ n (⟦subst⟧ σ n ⟦Δ⟧) >>= x) (ext λ l → ext λ ⟦A⟧ →
                begin
                    ⟦ traverse′ (σ ↓ˢ k ↑ k) C ⟧ᵐ l (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ l , ⟦A⟧)
                ≡⟨ traverse′-sound (σ ↓ˢ k ↑ k) C l (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ l , ⟦A⟧) ⟩
                    ⟦ C ⟧ᵐ l (⟦subst⟧ (_↑_ {A now} (σ ↓ˢ k) k) l (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ l , ⟦A⟧))
                ≡⟨ cong (⟦ C ⟧ᵐ l) (⟦↑⟧ (A now) (σ ↓ˢ k) l (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ l) ⟦A⟧) ⟩
                    ⟦ C ⟧ᵐ l (⟦subst⟧ (σ ↓ˢ k) l (⟦ Δ ⟧ˢₓ n ⟦Δ⟧ l) , ⟦A⟧)
                ≡⟨ cong (λ x → ⟦ C ⟧ᵐ l (x , ⟦A⟧)) (⟦subst⟧-⟦⟧ˢₓ σ n l ⟦Δ⟧) ⟩
                    ⟦ C ⟧ᵐ l (⟦ Γ ⟧ˢₓ n (⟦subst⟧ σ n ⟦Δ⟧) l , ⟦A⟧)
                ∎)
             ⟩
                ⟦ E ⟧ₘ n (⟦subst⟧ σ n ⟦Δ⟧) >>= (λ l ⟦A⟧ → ⟦ C ⟧ᵐ l (⟦ Γ ⟧ˢₓ n (⟦subst⟧ σ n ⟦Δ⟧) l , ⟦A⟧))
            ≡⟨⟩
                ⟦ letEvt E In C ⟧ᵐ n (⟦subst⟧ σ n ⟦Δ⟧)
            ∎
        traverse′-sound {_} {Δ} σ (select_↦_||_↦_||both↦_ {Γ} {A} {B} {C} E₁ C₁ E₂ C₂ C₃) n ⟦Δ⟧ =
            begin
                ⟦ traverse′ σ (select E₁ ↦ C₁ || E₂ ↦ C₂ ||both↦ C₃) ⟧ᵐ n ⟦Δ⟧
            ≡⟨⟩
                ⟦ select traverse σ E₁ ↦ traverse′ (σ ↓ˢ k ↑ k ↑ k) C₁
                      || traverse σ E₂ ↦ traverse′ (σ ↓ˢ k ↑ k ↑ k) C₂
                      ||both↦            traverse′ (σ ↓ˢ k ↑ k ↑ k) C₃ ⟧ᵐ n ⟦Δ⟧
            ≡⟨⟩
                (◇-select n (⟦ traverse σ E₁ ⟧ₘ n ⟦Δ⟧ , ⟦ traverse σ E₂ ⟧ₘ n ⟦Δ⟧)
                >>= ⟦select⟧ Δ A B C n ⟦Δ⟧
                        ⟦ traverse′ (σ ↓ˢ k ↑ k ↑ k) C₁ ⟧ᵐ
                        ⟦ traverse′ (σ ↓ˢ k ↑ k ↑ k) C₂ ⟧ᵐ
                        ⟦ traverse′ (σ ↓ˢ k ↑ k ↑ k) C₃ ⟧ᵐ)
            ≡⟨ cong (λ x → ◇-select n (⟦ traverse σ E₁ ⟧ₘ n ⟦Δ⟧ , ⟦ traverse σ E₂ ⟧ₘ n ⟦Δ⟧) >>= x)
                (ext λ l → ext λ c →
                begin
                    ⟦select⟧ Δ A B C n ⟦Δ⟧
                        ⟦ traverse′ (σ ↓ˢ k ↑ k ↑ k) C₁ ⟧ᵐ
                        ⟦ traverse′ (σ ↓ˢ k ↑ k ↑ k) C₂ ⟧ᵐ
                        ⟦ traverse′ (σ ↓ˢ k ↑ k ↑ k) C₃ ⟧ᵐ l c
                ≡⟨ ind-hyp l c ⟩
                    ⟦select⟧ Δ A B C n ⟦Δ⟧
                        (⟦ C₁ ⟧ᵐ ∘ (⟦subst⟧ (_↑_ {A now} (_↑_ {Event B now} (σ ↓ˢ k) k) k)))
                        (⟦ C₂ ⟧ᵐ ∘ (⟦subst⟧ (_↑_ {B now} (_↑_ {Event A now} (σ ↓ˢ k) k) k)))
                        (⟦ C₃ ⟧ᵐ ∘ (⟦subst⟧ (_↑_ {B now} (_↑_ {A now}       (σ ↓ˢ k) k) k))) l c
                ≡⟨ ⟦subst⟧-⟦select⟧ A B σ n l c ⟦Δ⟧ ⟩
                    ⟦select⟧ Γ A B C n (⟦subst⟧ σ n ⟦Δ⟧) ⟦ C₁ ⟧ᵐ ⟦ C₂ ⟧ᵐ ⟦ C₃ ⟧ᵐ l c
                ∎)
             ⟩
                ◇-select n ( ⟦ traverse σ E₁ ⟧ₘ n ⟦Δ⟧ , ⟦ traverse σ E₂ ⟧ₘ n ⟦Δ⟧)
                >>= ⟦select⟧ Γ A B C n (⟦subst⟧ σ n ⟦Δ⟧) ⟦ C₁ ⟧ᵐ ⟦ C₂ ⟧ᵐ ⟦ C₃ ⟧ᵐ
            ≡⟨ cong₂ (λ y z → ◇-select n (y , z) >>= _) (traverse-sound σ E₁ n ⟦Δ⟧)
                                                        (traverse-sound σ E₂ n ⟦Δ⟧) ⟩
                ◇-select n (⟦ E₁ ⟧ₘ n (⟦subst⟧ σ n ⟦Δ⟧) , ⟦ E₂ ⟧ₘ n (⟦subst⟧ σ n ⟦Δ⟧))
                >>= ⟦select⟧ Γ A B C n (⟦subst⟧ σ n ⟦Δ⟧) ⟦ C₁ ⟧ᵐ ⟦ C₂ ⟧ᵐ ⟦ C₃ ⟧ᵐ
            ≡⟨⟩
                ⟦ select E₁ ↦ C₁ || E₂ ↦ C₂ ||both↦ C₃ ⟧ᵐ n (⟦subst⟧ σ n ⟦Δ⟧)
            ∎
            where
            ind-hyp : ∀ l c
                -> ⟦select⟧ Δ A B C n ⟦Δ⟧
                        ⟦ traverse′ (σ ↓ˢ k ↑ k ↑ k) C₁ ⟧ᵐ
                        ⟦ traverse′ (σ ↓ˢ k ↑ k ↑ k) C₂ ⟧ᵐ
                        ⟦ traverse′ (σ ↓ˢ k ↑ k ↑ k) C₃ ⟧ᵐ l c
                 ≡ ⟦select⟧ Δ A B C n ⟦Δ⟧
                        (⟦ C₁ ⟧ᵐ ∘ (⟦subst⟧ (_↑_ {A now} (_↑_ {Event B now} (σ ↓ˢ k) k) k)))
                        (⟦ C₂ ⟧ᵐ ∘ (⟦subst⟧ (_↑_ {B now} (_↑_ {Event A now} (σ ↓ˢ k) k) k)))
                        (⟦ C₃ ⟧ᵐ ∘ (⟦subst⟧ (_↑_ {B now} (_↑_ {A now}       (σ ↓ˢ k) k) k))) l c
            ind-hyp l c rewrite ext (λ n -> (ext λ ⟦Δ⟧ -> (traverse′-sound (σ ↓ˢ k ↑ k ↑ k) C₁ n ⟦Δ⟧)))
                              | ext (λ n -> (ext λ ⟦Δ⟧ -> (traverse′-sound (σ ↓ˢ k ↑ k ↑ k) C₂ n ⟦Δ⟧)))
                              | ext (λ n -> (ext λ ⟦Δ⟧ -> (traverse′-sound (σ ↓ˢ k ↑ k ↑ k) C₃ n ⟦Δ⟧))) = refl
