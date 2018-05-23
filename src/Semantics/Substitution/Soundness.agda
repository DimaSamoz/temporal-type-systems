
-- Soundness proofs of structural lemmas and substitution
module Semantics.Substitution.Soundness where

open import Syntax.Types
open import Syntax.Context renaming (_,_ to _,,_)
open import Syntax.Terms
open import Syntax.Substitution.Kits
open import Syntax.Substitution.Instances
open import Syntax.Substitution.Lemmas

open import Semantics.Types
open import Semantics.Context
open import Semantics.Terms
open import Semantics.Substitution.Kits
open import Semantics.Substitution.Traversal
open import Semantics.Substitution.Instances

open import CategoryTheory.Categories using (Category ; ext)
open import CategoryTheory.Functor
open import CategoryTheory.NatTrans
open import CategoryTheory.Monad
open import CategoryTheory.Comonad
open import CategoryTheory.Instances.Reactive renaming (top to ⊤)
open import TemporalOps.Diamond
open import TemporalOps.Box
open import TemporalOps.OtherOps

open import Data.Sum
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as ≡
    using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; subst)

open ≡.≡-Reasoning
open import Holes.Term using (⌞_⌟)
open import Holes.Cong.Propositional


open ⟦K⟧ ⟦𝒯erm⟧

-- | Interpretation of various types of substitution as context morphisms

-- Denotation of term substitutions
⟦_⟧ₛ : ∀{Γ Δ} -> Subst Term Γ Δ -> ⟦ Δ ⟧ₓ ⇴ ⟦ Γ ⟧ₓ
⟦ σ ⟧ₛ = ⟦subst⟧ σ

-- Denotation of OPEs
⟦_⟧⊆ : ∀{Γ Δ} -> Γ ⊆ Δ -> ⟦ Δ ⟧ₓ ⇴ ⟦ Γ ⟧ₓ
⟦ s ⟧⊆ = ⟦ s ⊆ₛ 𝒯erm ⟧ₛ

-- Denotation of context exchange
⟦exch⟧ : ∀ Γ Γ′ Γ″ {A B} -> ⟦ Γ ⌊ B ⌋ Γ′ ⌊ A ⌋ Γ″ ⟧ₓ ⇴ ⟦ Γ ⌊ A ⌋ Γ′ ⌊ B ⌋ Γ″ ⟧ₓ
⟦exch⟧ Γ Γ′ Γ″ = ⟦ exₛ 𝒯ermₛ Γ Γ′ Γ″ ⟧ₛ

-- Denotation of context contraction
⟦contr⟧ : ∀ Γ Γ′ Γ″ {A} -> ⟦ Γ ⌊ A ⌋ Γ′ ⌊⌋ Γ″ ⟧ₓ ⇴ ⟦ Γ ⌊ A ⌋ Γ′ ⌊ A ⌋ Γ″ ⟧ₓ
⟦contr⟧ Γ Γ′ Γ″ = ⟦ contr-lₛ 𝒯ermₛ Γ Γ′ Γ″ ⟧ₛ

-- Denotation of middle context substitution
⟦_⌊⌋ₛ_⊢ₛ_⟧ : ∀ Γ Γ′ {A} -> Γ ⌊⌋ Γ′ ⊢ A -> ⟦ Γ ⌊⌋ Γ′ ⟧ₓ ⇴ ⟦ Γ ⌊ A ⌋ Γ′ ⟧ₓ
⟦ Γ ⌊⌋ₛ Γ′ ⊢ₛ M ⟧ = ⟦ sub-midₛ 𝒯ermₛ Γ Γ′ M ⟧ₛ

-- Denotational soundness of top substitution
⟦sub-topₛ⟧ : ∀ {Γ A} -> (M : Γ ⊢ A)
        -> ⟦ sub-topₛ 𝒯ermₛ M ⟧ₛ ≈ ⟨ id , ⟦ M ⟧ₘ ⟩
⟦sub-topₛ⟧ {Γ} M {n} {⟦Γ⟧} rewrite ⟦idₛ⟧ {Γ} {n} {⟦Γ⟧} = refl

-- | Soundness theorems
-- | Concrete soundness theorems for structural lemmas and substitution
-- | are instances of the general traversal soundness proof

-- Substituting traversal is sound
substitute-sound : ∀{Γ Δ A} (σ : Subst Term Γ Δ) (M : Γ ⊢ A)
                -> ⟦ substitute σ M ⟧ₘ ≈ ⟦ M ⟧ₘ ∘ ⟦ σ ⟧ₛ
substitute-sound σ M = traverse-sound ⟦𝒯erm⟧ σ M

substitute′-sound : ∀{Γ Δ A} (σ : Subst Term Γ Δ) (M : Γ ⊨ A)
                -> ⟦ substitute′ σ M ⟧ᵐ ≈ ⟦ M ⟧ᵐ ∘ ⟦ σ ⟧ₛ
substitute′-sound σ M = traverse′-sound ⟦𝒯erm⟧ σ M

-- Weakening lemma is sound
weakening-sound : ∀{Γ Δ A} (s : Γ ⊆ Δ) (M : Γ ⊢ A)
               -> ⟦ weakening s M ⟧ₘ ≈ ⟦ M ⟧ₘ ∘ ⟦ s ⟧⊆
weakening-sound s = substitute-sound (s ⊆ₛ 𝒯erm)

-- Exchange lemma is sound
exchange-sound : ∀{Γ Γ′ Γ″ A B C} (M : Γ ⌊ A ⌋ Γ′ ⌊ B ⌋ Γ″ ⊢ C)
              -> ⟦ exchange Γ Γ′ Γ″ M ⟧ₘ ≈ ⟦ M ⟧ₘ ∘ (⟦exch⟧ Γ Γ′ Γ″)
exchange-sound {Γ} {Γ′} {Γ″} = substitute-sound (exₛ 𝒯ermₛ Γ Γ′ Γ″)

-- Contraction lemma is sound
contraction-sound : ∀{Γ Γ′ Γ″ A B} (M : Γ ⌊ A ⌋ Γ′ ⌊ A ⌋ Γ″ ⊢ B)
                 -> ⟦ contraction Γ Γ′ Γ″ M ⟧ₘ ≈ ⟦ M ⟧ₘ ∘ (⟦contr⟧ Γ Γ′ Γ″)
contraction-sound {Γ} {Γ′} {Γ″} = substitute-sound (contr-lₛ 𝒯ermₛ Γ Γ′ Γ″)

-- Substitution lemma is sound
substitution-sound : ∀{Γ Γ′ A B} (M : Γ ⌊⌋ Γ′ ⊢ A) (N : Γ ⌊ A ⌋ Γ′ ⊢ B)
                 -> ⟦ substitution Γ Γ′ M N ⟧ₘ ≈ ⟦ N ⟧ₘ ∘ ⟦ Γ ⌊⌋ₛ Γ′ ⊢ₛ M ⟧
substitution-sound {Γ} {Γ′} M = substitute-sound (sub-midₛ 𝒯ermₛ Γ Γ′ M)

-- Substitution lemma is sound
substitution′-sound : ∀{Γ Γ′ A B} (M : Γ ⌊⌋ Γ′ ⊢ A) (N : Γ ⌊ A ⌋ Γ′ ⊨ B)
                 -> ⟦ substitution′ Γ Γ′ M N ⟧ᵐ ≈ ⟦ N ⟧ᵐ ∘ ⟦ Γ ⌊⌋ₛ Γ′ ⊢ₛ M ⟧
substitution′-sound {Γ} {Γ′} M N = traverse′-sound ⟦𝒯erm⟧ (sub-midₛ 𝒯ermₛ Γ Γ′ M) N

-- Top substitution is sound (full categorical proof)
subst-sound : ∀{Γ A B} (M : Γ ⊢ A) (N : Γ ,, A ⊢ B)
           -> ⟦ [ M /] N ⟧ₘ ≈ ⟦ N ⟧ₘ ∘ ⟨ id , ⟦ M ⟧ₘ ⟩
subst-sound M N {n} {a} rewrite sym (⟦sub-topₛ⟧ M {n} {a}) =
    substitute-sound (sub-topₛ 𝒯ermₛ M) N

-- Top substitution is sound (full categorical proof)
subst′-sound : ∀{Γ A B} (M : Γ ⊢ A) (N : Γ ,, A ⊨ B)
           -> ⟦ [ M /′] N ⟧ᵐ ≈ ⟦ N ⟧ᵐ ∘ ⟨ id , ⟦ M ⟧ₘ ⟩
subst′-sound M N {n} {a} rewrite sym (⟦sub-topₛ⟧ M {n} {a}) =
    traverse′-sound ⟦𝒯erm⟧ (sub-topₛ 𝒯ermₛ M) N

open K 𝒯erm
open Monad M-◇
open Comonad W-□
private module F-□ = Functor F-□

-- Lemma used in the soundness proof of computational substitution
subst″-sound-lemma : ∀ Γ {A B} (n k l : ℕ)
                    -> (D : Γ ˢ ,, A now ⊨ B now)
                    -> (⟦Γ⟧ : ⟦ Γ ⟧ₓ n) (⟦A⟧ : ⟦ A ⟧ₜ l)
                  -> ⟦ substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D ⟧ᵐ l (⟦ Γ ˢ ˢ⟧□ k (⟦ Γ ˢ⟧□ n ⟦Γ⟧ k) l , ⟦A⟧)
                   ≡ ⟦ D ⟧ᵐ l (⟦ Γ ˢ⟧□ n ⟦Γ⟧ l , ⟦A⟧)
subst″-sound-lemma Γ {A} n k l D ⟦Γ⟧ ⟦A⟧
    rewrite substitute′-sound ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D {l} {⟦ Γ ˢ ˢ⟧□ k (⟦ Γ ˢ⟧□ n ⟦Γ⟧ k) l , ⟦A⟧}
          | ⟦↑⟧ (A now) (Γ ˢˢₛ 𝒯erm) {l} {⟦ Γ ˢ ˢ⟧□ k (⟦ Γ ˢ⟧□ n ⟦Γ⟧ k) l , ⟦A⟧}
          | □-≡ k l (□-≡ n k (⟦ˢ⟧□-twice Γ {n} {⟦Γ⟧}) k) l
          | □-≡ k l (⟦ˢˢ⟧ Γ {n} {⟦Γ⟧}) l = refl

-- Substitution of a computation into a computation is sound
subst″-sound : ∀{Γ A B} (C : Γ ⊨ A now) (D : Γ ˢ ,, A now ⊨ B now)
            -> (n : ℕ) (⟦Γ⟧ : ⟦ Γ ⟧ₓ n)
            -> ⟦ ⟨ C /⟩ D ⟧ᵐ n ⟦Γ⟧
             ≡ (⟦ C ⟧ᵐ n ⟦Γ⟧ >>= λ l ⟦A⟧ → ⟦ D ⟧ᵐ l ((⟦ Γ ˢ⟧□ n ⟦Γ⟧ l) , ⟦A⟧))
subst″-sound {Γ} (pure {A = A} M) D n ⟦Γ⟧ =
    begin
        ⟦ ⟨ pure M /⟩ D ⟧ᵐ n ⟦Γ⟧
    ≡⟨⟩
        ⟦ traverse′ (sub-topˢₛ 𝒯ermₛ M) D ⟧ᵐ n ⟦Γ⟧
    ≡⟨ traverse′-sound ⟦𝒯erm⟧ (sub-topˢₛ 𝒯ermₛ M) D {n} {⟦Γ⟧} ⟩
        ⟦ D ⟧ᵐ n (⌞ ⟦subst⟧ (Γˢ⊆Γ Γ ⊆ₛ 𝒯erm) n ⟦Γ⟧ ⌟ , ⟦ M ⟧ₘ n ⟦Γ⟧)
    ≡⟨ cong!
        (begin
            ⟦ Γˢ⊆Γ Γ ⟧⊆ n ⟦Γ⟧
        ≡⟨ lemma Γ n ⟦Γ⟧ ⟩
            ⟦ Γ ˢ⟧□ n ⟦Γ⟧ n
        ∎)
     ⟩
        ⟦ D ⟧ᵐ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ n , ⟦ M ⟧ₘ n ⟦Γ⟧)
    ≡⟨ η-unit1 ⟩
        (η.at ⟦ A ⟧ⱼ n (⟦ M ⟧ₘ n ⟦Γ⟧) >>= (λ l ⟦A⟧ → ⟦ D ⟧ᵐ l (⟦ Γ ˢ⟧□ n ⟦Γ⟧ l , ⟦A⟧)))
    ≡⟨⟩
        (⟦ pure M ⟧ᵐ n ⟦Γ⟧ >>= (λ l ⟦A⟧ → ⟦ D ⟧ᵐ l (⟦ Γ ˢ⟧□ n ⟦Γ⟧ l , ⟦A⟧)))
    ∎
    where
    lemma : ∀ Γ n ⟦Γ⟧ -> ⟦ Γˢ⊆Γ Γ ⟧⊆ n ⟦Γ⟧ ≡ ⟦ Γ ˢ⟧□ n ⟦Γ⟧ n
    lemma ∙ n ⟦Γ⟧ = refl
    lemma (Γ ,, B now) n (⟦Γ⟧ , ⟦B⟧)
            rewrite ⟦⁺⟧ (B now) (Γˢ⊆Γ Γ ⊆ₛ 𝒯erm) {n} {⟦Γ⟧ , ⟦B⟧}
                  | lemma Γ n ⟦Γ⟧ = refl
    lemma (Γ ,, B always) n (⟦Γ⟧ , ⟦B⟧)
            rewrite ⟦↑⟧ (B always) (Γˢ⊆Γ Γ ⊆ₛ 𝒯erm) {n} {⟦Γ⟧ , ⟦B⟧}
                  | lemma Γ n ⟦Γ⟧ = refl

subst″-sound {Γ} {A} (letSig_InC_ {A = B} S C) D n ⟦Γ⟧ =
    begin
        ⟦ ⟨ letSig S InC C /⟩ D ⟧ᵐ n ⟦Γ⟧
    ≡⟨⟩
        ⟦ ⟨ C /⟩ (substitute′ (idₛ 𝒯erm ⁺ 𝒯erm ↑ 𝒯erm) D) ⟧ᵐ n (⟦Γ⟧ , ⟦ S ⟧ₘ n ⟦Γ⟧)
    ≡⟨ subst″-sound C (substitute′ (idₛ 𝒯erm ⁺ 𝒯erm ↑ 𝒯erm) D) n (⟦Γ⟧ , ⟦ S ⟧ₘ n ⟦Γ⟧) ⟩
        ⟦ C ⟧ᵐ n (⟦Γ⟧ , ⟦ S ⟧ₘ n ⟦Γ⟧)
        >>= (λ l ⟦A⟧ → ⟦ substitute′ (idₛ 𝒯erm ⁺ 𝒯erm ↑ 𝒯erm) D ⟧ᵐ l ((⟦ Γ ˢ⟧□ n ⟦Γ⟧ l , ⟦ S ⟧ₘ n ⟦Γ⟧) , ⟦A⟧))
    ≡⟨ cong (λ x → (⟦ C ⟧ᵐ n (⟦Γ⟧ , ⟦ S ⟧ₘ n ⟦Γ⟧) >>= x))
        (ext λ l → ext λ ⟦A⟧ →
            begin
                ⟦ substitute′ (idₛ 𝒯erm ⁺ 𝒯erm ↑ 𝒯erm) D ⟧ᵐ l ((⟦ Γ ˢ⟧□ n ⟦Γ⟧ l , ⟦ S ⟧ₘ n ⟦Γ⟧) , ⟦A⟧)
            ≡⟨ substitute′-sound (_↑_ {A now} (_⁺_ {B always} (idₛ 𝒯erm) 𝒯erm) 𝒯erm) D {l} {((⟦ Γ ˢ⟧□ n ⟦Γ⟧ l , ⟦ S ⟧ₘ n ⟦Γ⟧) , ⟦A⟧)} ⟩
                ⟦ D ⟧ᵐ l (⟦ (_↑_ {A now} {Γ = Γ ˢ} (_⁺_ {B always} (idₛ 𝒯erm) 𝒯erm) 𝒯erm) ⟧ₛ l ((⟦ Γ ˢ⟧□ n ⟦Γ⟧ l , ⟦ S ⟧ₘ n ⟦Γ⟧) , ⟦A⟧))
            ≡⟨ cong (⟦ D ⟧ᵐ l) (⟦↑⟧ (A now) {Γ ˢ ,, B always} (_⁺_ {B always} (idₛ 𝒯erm) 𝒯erm) {l} {(⟦ Γ ˢ⟧□ n ⟦Γ⟧ l , ⟦ S ⟧ₘ n ⟦Γ⟧) , ⟦A⟧}) ⟩
                ⟦ D ⟧ᵐ l (⟦ _⁺_ {B always} {Γ = Γ ˢ} (idₛ 𝒯erm) 𝒯erm ⟧ₛ l (⟦ Γ ˢ⟧□ n ⟦Γ⟧ l , ⟦ S ⟧ₘ n ⟦Γ⟧) , ⟦A⟧)
            ≡⟨ cong (λ x → ⟦ D ⟧ᵐ l (x , ⟦A⟧)) (⟦⁺⟧ (B always) {Γ ˢ} (idₛ 𝒯erm) {l} {⟦ Γ ˢ⟧□ n ⟦Γ⟧ l , ⟦ S ⟧ₘ n ⟦Γ⟧}) ⟩
                ⟦ D ⟧ᵐ l (⟦ idₛ {Γ ˢ} 𝒯erm ⟧ₛ l (⟦ Γ ˢ⟧□ n ⟦Γ⟧ l) , ⟦A⟧)
            ≡⟨ cong (λ x → ⟦ D ⟧ᵐ l (x , ⟦A⟧)) (⟦idₛ⟧ {Γ ˢ} {l} {⟦ Γ ˢ⟧□ n ⟦Γ⟧ l}) ⟩
                ⟦ D ⟧ᵐ l (⟦ Γ ˢ⟧□ n ⟦Γ⟧ l , ⟦A⟧)
            ∎
        )
     ⟩
        ⟦ letSig S InC C ⟧ᵐ n ⟦Γ⟧
        >>= (λ l ⟦A⟧ → ⟦ D ⟧ᵐ l (⟦ Γ ˢ⟧□ n ⟦Γ⟧ l , ⟦A⟧))
    ∎

subst″-sound {Γ} {A} {B} (letEvt E In C) D n ⟦Γ⟧ =
    begin
        ⟦ ⟨ letEvt E In C /⟩ D ⟧ᵐ n ⟦Γ⟧
    ≡⟨⟩
        ⟦ E ⟧ₘ n ⟦Γ⟧
            >>= (λ k ⟦A⟧ → ⟦ ⟨ C /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) ⟧ᵐ k (⟦ Γ ˢ⟧□ n ⟦Γ⟧ k , ⟦A⟧))
    ≡⟨ cong (λ x → ⟦ E ⟧ₘ n ⟦Γ⟧ >>= x)
        (ext λ k → ext λ ⟦A⟧ → (begin
            ⟦ ⟨ C /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) ⟧ᵐ k (⟦ Γ ˢ⟧□ n ⟦Γ⟧ k , ⟦A⟧)
        ≡⟨ subst″-sound C (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) k (⟦ Γ ˢ⟧□ n ⟦Γ⟧ k , ⟦A⟧) ⟩
            ⟦ C ⟧ᵐ k (⟦ Γ ˢ⟧□ n ⟦Γ⟧ k , ⟦A⟧)
            >>= (λ l ⟦A⟧₁ → ⟦ substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D ⟧ᵐ l (⟦ Γ ˢ ˢ⟧□ k (⟦ Γ ˢ⟧□ n ⟦Γ⟧ k) l , ⟦A⟧₁))
        ≡⟨ cong (λ x → ⟦ C ⟧ᵐ k (⟦ Γ ˢ⟧□ n ⟦Γ⟧ k , ⟦A⟧) >>= x)
                (ext λ l → ext λ ⟦A⟧₁ → subst″-sound-lemma Γ n k l D ⟦Γ⟧ ⟦A⟧₁) ⟩
            ⟦ C ⟧ᵐ k (⟦ Γ ˢ⟧□ n ⟦Γ⟧ k , ⟦A⟧)
            >>= (λ l ⟦A⟧₁ → ⟦ D ⟧ᵐ l (⟦ Γ ˢ⟧□ n ⟦Γ⟧ l , ⟦A⟧₁))
        ∎)) ⟩
        ⟦ E ⟧ₘ n ⟦Γ⟧
            >>= (λ k ⟦A⟧ → ⟦ C ⟧ᵐ k (⟦ Γ ˢ⟧□ n ⟦Γ⟧ k , ⟦A⟧)
                >>=  λ l ⟦A⟧ → ⟦ D ⟧ᵐ l (⟦ Γ ˢ⟧□ n ⟦Γ⟧ l , ⟦A⟧))
    ≡⟨ sym (>>=-assoc (⟦ E ⟧ₘ n ⟦Γ⟧) _ _) ⟩
        (⟦ E ⟧ₘ n ⟦Γ⟧
            >>= λ k ⟦A⟧ → ⟦ C ⟧ᵐ k (⟦ Γ ˢ⟧□ n ⟦Γ⟧ k , ⟦A⟧))
        >>= (λ l ⟦A⟧ → ⟦ D ⟧ᵐ l (⟦ Γ ˢ⟧□ n ⟦Γ⟧ l , ⟦A⟧))
    ≡⟨⟩
        (⟦ letEvt E In C ⟧ᵐ n ⟦Γ⟧
        >>= (λ l ⟦A⟧ → ⟦ D ⟧ᵐ l (⟦ Γ ˢ⟧□ n ⟦Γ⟧ l , ⟦A⟧)))
    ∎

subst″-sound {B = E} (select_↦_||_↦_||both↦_ {Γ}{A}{B}{C} E₁ C₁ E₂ C₂ C₃) D n ⟦Γ⟧ =
    begin
        ⟦ ⟨ select E₁ ↦ C₁ || E₂ ↦ C₂ ||both↦ C₃ /⟩ D ⟧ᵐ n ⟦Γ⟧
    ≡⟨⟩
        ⟦ select E₁ ↦ ⟨ C₁ /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D)
              || E₂ ↦ ⟨ C₂ /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D)
              ||both↦ ⟨ C₃ /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) ⟧ᵐ n ⟦Γ⟧
    ≡⟨⟩
        ◇-select n (⟦ E₁ ⟧ₘ n ⟦Γ⟧ , ⟦ E₂ ⟧ₘ n ⟦Γ⟧)
        >>= ⟦select⟧ Γ A B E n ⟦Γ⟧
                ⟦ ⟨ C₁ /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) ⟧ᵐ
                ⟦ ⟨ C₂ /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) ⟧ᵐ
                ⟦ ⟨ C₃ /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) ⟧ᵐ

    ≡⟨ cong (λ x -> ◇-select n (⟦ E₁ ⟧ₘ n ⟦Γ⟧ , ⟦ E₂ ⟧ₘ n ⟦Γ⟧) >>= x) (ext λ m → ext λ c →
        (begin
            ⟦select⟧ Γ A B E n ⟦Γ⟧
                ⟦ ⟨ C₁ /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) ⟧ᵐ
                ⟦ ⟨ C₂ /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) ⟧ᵐ
                ⟦ ⟨ C₃ /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) ⟧ᵐ m c
        ≡⟨ lemma m c ⟩
            (⟦select⟧ Γ A B C n ⟦Γ⟧ ⟦ C₁ ⟧ᵐ ⟦ C₂ ⟧ᵐ ⟦ C₃ ⟧ᵐ m c
                >>= λ l ⟦A⟧ → ⟦ D ⟧ᵐ l (⟦ Γ ˢ⟧□ n ⟦Γ⟧ l , ⟦A⟧))
        ∎))
     ⟩
        ◇-select n (⟦ E₁ ⟧ₘ n ⟦Γ⟧ , ⟦ E₂ ⟧ₘ n ⟦Γ⟧)
            >>= (λ m c → ⟦select⟧ Γ A B C n ⟦Γ⟧ ⟦ C₁ ⟧ᵐ ⟦ C₂ ⟧ᵐ ⟦ C₃ ⟧ᵐ m c
                >>= λ l ⟦A⟧ → ⟦ D ⟧ᵐ l (⟦ Γ ˢ⟧□ n ⟦Γ⟧ l , ⟦A⟧))
    ≡⟨ sym (>>=-assoc (◇-select n (⟦ E₁ ⟧ₘ n ⟦Γ⟧ , ⟦ E₂ ⟧ₘ n ⟦Γ⟧)) _ _) ⟩
        (◇-select n (⟦ E₁ ⟧ₘ n ⟦Γ⟧ , ⟦ E₂ ⟧ₘ n ⟦Γ⟧)
            >>= ⟦select⟧ Γ A B C n ⟦Γ⟧ ⟦ C₁ ⟧ᵐ ⟦ C₂ ⟧ᵐ ⟦ C₃ ⟧ᵐ)
        >>= (λ l ⟦A⟧ → ⟦ D ⟧ᵐ l (⟦ Γ ˢ⟧□ n ⟦Γ⟧ l , ⟦A⟧))
    ≡⟨⟩
        ⟦ select E₁ ↦ C₁ || E₂ ↦ C₂ ||both↦ C₃ ⟧ᵐ n ⟦Γ⟧
        >>= (λ l ⟦A⟧ → ⟦ D ⟧ᵐ l (⟦ Γ ˢ⟧□ n ⟦Γ⟧ l , ⟦A⟧))
    ∎
    where
    lemma : ∀ m c
           -> ⟦select⟧ Γ A B E n ⟦Γ⟧
               ⟦ ⟨ C₁ /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) ⟧ᵐ
               ⟦ ⟨ C₂ /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) ⟧ᵐ
               ⟦ ⟨ C₃ /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) ⟧ᵐ m c
            ≡ (⟦select⟧ Γ A B C n ⟦Γ⟧ ⟦ C₁ ⟧ᵐ ⟦ C₂ ⟧ᵐ ⟦ C₃ ⟧ᵐ m c
                >>= λ l ⟦A⟧ → ⟦ D ⟧ᵐ l (⟦ Γ ˢ⟧□ n ⟦Γ⟧ l , ⟦A⟧))
    lemma m (inj₁ (inj₁ (⟦A⟧ , ⟦◇B⟧)))
        rewrite subst″-sound C₁ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) m ((⟦ Γ ˢ⟧□ n ⟦Γ⟧ m , ⟦◇B⟧) , ⟦A⟧)
              | (ext λ l → ext λ ⟦C⟧ → subst″-sound-lemma Γ n m l D ⟦Γ⟧ ⟦C⟧)
        = refl

    lemma m (inj₁ (inj₂ (⟦◇A⟧ , ⟦B⟧)))
        rewrite subst″-sound C₂ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) m ((⟦ Γ ˢ⟧□ n ⟦Γ⟧ m , ⟦◇A⟧) , ⟦B⟧)
              | (ext λ l → ext λ ⟦C⟧ → subst″-sound-lemma Γ n m l D ⟦Γ⟧ ⟦C⟧)
        = refl
    lemma m (inj₂ (⟦A⟧ , ⟦B⟧))
        rewrite subst″-sound C₃ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) m ((⟦ Γ ˢ⟧□ n ⟦Γ⟧ m , ⟦A⟧) , ⟦B⟧)
              | (ext λ l → ext λ ⟦C⟧ → subst″-sound-lemma Γ n m l D ⟦Γ⟧ ⟦C⟧)
        = refl
