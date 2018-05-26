
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
open import Semantics.Bind

open import CategoryTheory.Categories using (Category ; ext)
open import CategoryTheory.Functor
open import CategoryTheory.NatTrans
open import CategoryTheory.Monad
open import CategoryTheory.Comonad
open import CategoryTheory.Linear
open import CategoryTheory.Instances.Reactive renaming (top to ⊤)
open import TemporalOps.Diamond
open import TemporalOps.Box
open import TemporalOps.OtherOps
open import TemporalOps.StrongMonad
open import TemporalOps.Linear

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
open Functor F-□ renaming (fmap to □-f)
open Functor F-◇ renaming (fmap to ◇-f)
private module F-◇ = Functor F-◇

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

subst″-sound : ∀{Γ A B} (C : Γ ⊨ A now) (D : Γ ˢ ,, A now ⊨ B now)
            -> ⟦ ⟨ C /⟩ D ⟧ᵐ ≈ bindEvent Γ ⟦ C ⟧ᵐ ⟦ D ⟧ᵐ
subst″-sound {Γ}{A}{B} (pure M) D {n} {⟦Γ⟧}
    rewrite traverse′-sound ⟦𝒯erm⟧ (sub-topˢₛ 𝒯ermₛ M) D {n} {⟦Γ⟧}
          | ⟦subst⟧-Γˢ⊆Γ Γ {n} {⟦Γ⟧} | ⟦ˢ⟧-factor Γ {n} {⟦Γ⟧} = refl
subst″-sound {Γ}{A}{B} (letSig_InC_ {A = G} S C) D {n} {⟦Γ⟧}
    rewrite subst″-sound C (substitute′ (idₛ 𝒯erm ⁺ 𝒯erm ↑ 𝒯erm) D) {n} {⟦Γ⟧ , ⟦ S ⟧ₘ n ⟦Γ⟧}
    =
    begin
        bindEvent (Γ ,, G always) ⟦ C ⟧ᵐ ⌞ ⟦ substitute′ ((_⁺_ {G always} (idₛ 𝒯erm) 𝒯erm) ↑ 𝒯erm) D ⟧ᵐ ⌟ n (⟦Γ⟧ , ⟦ S ⟧ₘ n ⟦Γ⟧)
    ≡⟨ bind-to->>= (Γ ,, G always) ⟦ C ⟧ᵐ ⟦ substitute′ ((_⁺_ {G always} (idₛ 𝒯erm) 𝒯erm) ↑ 𝒯erm) D ⟧ᵐ n (⟦Γ⟧ , ⟦ S ⟧ₘ n ⟦Γ⟧) ⟩
            ⟦ C ⟧ᵐ n (⟦Γ⟧ , ⟦ S ⟧ₘ n ⟦Γ⟧)
            >>= (λ l ⟦A⟧ → ⟦ substitute′ (idₛ 𝒯erm ⁺ 𝒯erm ↑ 𝒯erm) D ⟧ᵐ l ((⟦ Γ ˢ⟧□ n ⟦Γ⟧ l , ⟦ S ⟧ₘ n ⟦Γ⟧) , ⟦A⟧))
    ≡⟨ cong (λ x → (⟦ C ⟧ᵐ n (⟦Γ⟧ , ⟦ S ⟧ₘ n ⟦Γ⟧) >>= x))
        (ext λ l → ext λ ⟦A⟧ →
            begin
                ⟦ substitute′ (idₛ 𝒯erm ⁺ 𝒯erm ↑ 𝒯erm) D ⟧ᵐ l ((⟦ Γ ˢ⟧□ n ⟦Γ⟧ l , ⟦ S ⟧ₘ n ⟦Γ⟧) , ⟦A⟧)
            ≡⟨ substitute′-sound (_↑_ {A now} (_⁺_ {G always} (idₛ 𝒯erm) 𝒯erm) 𝒯erm) D {l} {((⟦ Γ ˢ⟧□ n ⟦Γ⟧ l , ⟦ S ⟧ₘ n ⟦Γ⟧) , ⟦A⟧)} ⟩
                ⟦ D ⟧ᵐ l (⟦ (_↑_ {A now} {Γ = Γ ˢ} (_⁺_ {G always} (idₛ 𝒯erm) 𝒯erm) 𝒯erm) ⟧ₛ l ((⟦ Γ ˢ⟧□ n ⟦Γ⟧ l , ⟦ S ⟧ₘ n ⟦Γ⟧) , ⟦A⟧))
            ≡⟨ cong (⟦ D ⟧ᵐ l) (⟦↑⟧ (A now) {Γ ˢ ,, G always} (_⁺_ {G always} (idₛ 𝒯erm) 𝒯erm) {l} {(⟦ Γ ˢ⟧□ n ⟦Γ⟧ l , ⟦ S ⟧ₘ n ⟦Γ⟧) , ⟦A⟧}) ⟩
                ⟦ D ⟧ᵐ l (⟦ _⁺_ {G always} {Γ = Γ ˢ} (idₛ 𝒯erm) 𝒯erm ⟧ₛ l (⟦ Γ ˢ⟧□ n ⟦Γ⟧ l , ⟦ S ⟧ₘ n ⟦Γ⟧) , ⟦A⟧)
            ≡⟨ cong (λ x → ⟦ D ⟧ᵐ l (x , ⟦A⟧)) (⟦⁺⟧ (G always) {Γ ˢ} (idₛ 𝒯erm) {l} {⟦ Γ ˢ⟧□ n ⟦Γ⟧ l , ⟦ S ⟧ₘ n ⟦Γ⟧}) ⟩
                ⟦ D ⟧ᵐ l (⟦ idₛ {Γ ˢ} 𝒯erm ⟧ₛ l (⟦ Γ ˢ⟧□ n ⟦Γ⟧ l) , ⟦A⟧)
            ≡⟨ cong (λ x → ⟦ D ⟧ᵐ l (x , ⟦A⟧)) (⟦idₛ⟧ {Γ ˢ} {l} {⟦ Γ ˢ⟧□ n ⟦Γ⟧ l}) ⟩
                ⟦ D ⟧ᵐ l (⟦ Γ ˢ⟧□ n ⟦Γ⟧ l , ⟦A⟧)
            ∎
        )
     ⟩
        ⟦ letSig S InC C ⟧ᵐ n ⟦Γ⟧
        >>= (λ l ⟦A⟧ → ⟦ D ⟧ᵐ l (⟦ Γ ˢ⟧□ n ⟦Γ⟧ l , ⟦A⟧))
    ≡⟨ sym (bind-to->>= Γ ⟦ letSig S InC C ⟧ᵐ ⟦ D ⟧ᵐ n ⟦Γ⟧) ⟩
        bindEvent Γ ⟦ letSig S InC C ⟧ᵐ ⟦ D ⟧ᵐ n ⟦Γ⟧
    ∎


subst″-sound {Γ}{A}{B} (letEvt_In_ {A = G} E C) D {n} {⟦Γ⟧} =
    begin
        ⟦ ⟨ letEvt E In C /⟩ D ⟧ᵐ n ⟦Γ⟧
    ≡⟨ bind-to->>= Γ ⟦ E ⟧ₘ ⟦ ⟨ C /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) ⟧ᵐ n ⟦Γ⟧ ⟩
        ⟦ E ⟧ₘ n ⟦Γ⟧
            >>= (λ k ⟦A⟧ → ⟦ ⟨ C /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) ⟧ᵐ k (⟦ Γ ˢ⟧□ n ⟦Γ⟧ k , ⟦A⟧))
    ≡⟨ cong (λ x → ⟦ E ⟧ₘ n ⟦Γ⟧ >>= x)
        (ext λ k → ext λ ⟦A⟧ → (begin
            ⟦ ⟨ C /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) ⟧ᵐ k (⟦ Γ ˢ⟧□ n ⟦Γ⟧ k , ⟦A⟧)
        ≡⟨ subst″-sound C (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) {k} {⟦ Γ ˢ⟧□ n ⟦Γ⟧ k , ⟦A⟧} ⟩
            bindEvent (Γ ˢ ,, G now) ⟦ C ⟧ᵐ
                ⟦ substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D ⟧ᵐ k (⟦ Γ ˢ⟧□ n ⟦Γ⟧ k , ⟦A⟧)
        ≡⟨ bind-to->>= (Γ ˢ ,, G now) ⟦ C ⟧ᵐ ⟦ substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D ⟧ᵐ k (⟦ Γ ˢ⟧□ n ⟦Γ⟧ k , ⟦A⟧) ⟩
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
    ≡⟨ cong (λ x -> x >>= _) (sym (bind-to->>= Γ ⟦ E ⟧ₘ ⟦ C ⟧ᵐ n ⟦Γ⟧)) ⟩
        (⟦ letEvt E In C ⟧ᵐ n ⟦Γ⟧
            >>= (λ l ⟦A⟧ → ⟦ D ⟧ᵐ l (⟦ Γ ˢ⟧□ n ⟦Γ⟧ l , ⟦A⟧)))
    ≡⟨ sym (bind-to->>= Γ ⟦ letEvt E In C ⟧ᵐ ⟦ D ⟧ᵐ n ⟦Γ⟧) ⟩
        bindEvent Γ ⟦ letEvt E In C ⟧ᵐ ⟦ D ⟧ᵐ n ⟦Γ⟧
    ∎


subst″-sound {Γ}{A}{B} (select_↦_||_↦_||both↦_ {A = G}{H} E₁ C₁ E₂ C₂ C₃) D {n} {⟦Γ⟧} =
    begin
        ⟦ ⟨ select E₁ ↦ C₁ || E₂ ↦ C₂ ||both↦ C₃ /⟩ D ⟧ᵐ n ⟦Γ⟧
    ≡⟨⟩
        ⟦ select E₁ ↦ ⟨ C₁ /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D)
              || E₂ ↦ ⟨ C₂ /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D)
              ||both↦ ⟨ C₃ /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) ⟧ᵐ n ⟦Γ⟧
    ≡⟨⟩
        bindEvent Γ (⟪ ⟦ E₁ ⟧ₘ , ⟦ E₂ ⟧ₘ ⟫) (handle
            ⟦ ⟨ C₁ /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) ⟧ᵐ
            ⟦ ⟨ C₂ /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) ⟧ᵐ
            ⟦ ⟨ C₃ /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) ⟧ᵐ) n ⟦Γ⟧
    ≡⟨ bind-to->>= Γ (⟪ ⟦ E₁ ⟧ₘ , ⟦ E₂ ⟧ₘ ⟫) (handle
                ⟦ ⟨ C₁ /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) ⟧ᵐ
                ⟦ ⟨ C₂ /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) ⟧ᵐ
                ⟦ ⟨ C₃ /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) ⟧ᵐ) n ⟦Γ⟧ ⟩
        ⟪ ⟦ E₁ ⟧ₘ , ⟦ E₂ ⟧ₘ ⟫ n ⟦Γ⟧
        >>= (λ l ⟦A⟧ → handle
                ⟦ ⟨ C₁ /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) ⟧ᵐ
                ⟦ ⟨ C₂ /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) ⟧ᵐ
                ⟦ ⟨ C₃ /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) ⟧ᵐ l (⟦ Γ ˢ⟧□ n ⟦Γ⟧ l , ⟦A⟧))
    ≡⟨ cong (λ x → ⟪ ⟦ E₁ ⟧ₘ , ⟦ E₂ ⟧ₘ ⟫ n ⟦Γ⟧ >>= x) (ext λ m → ext λ c → lemma m c) ⟩
        ⟪ ⟦ E₁ ⟧ₘ , ⟦ E₂ ⟧ₘ ⟫ n ⟦Γ⟧
            >>= (λ m c → handle ⟦ C₁ ⟧ᵐ ⟦ C₂ ⟧ᵐ ⟦ C₃ ⟧ᵐ m (⟦ Γ ˢ⟧□ n ⟦Γ⟧ m , c)
                >>= λ l ⟦A⟧ → ⟦ D ⟧ᵐ l (⟦ Γ ˢ⟧□ n ⟦Γ⟧ l , ⟦A⟧))
    ≡⟨ sym (>>=-assoc (⟪ ⟦ E₁ ⟧ₘ , ⟦ E₂ ⟧ₘ ⟫ n ⟦Γ⟧) _ _) ⟩
        (⟪ ⟦ E₁ ⟧ₘ , ⟦ E₂ ⟧ₘ ⟫ n ⟦Γ⟧
            >>= λ m c -> handle ⟦ C₁ ⟧ᵐ ⟦ C₂ ⟧ᵐ ⟦ C₃ ⟧ᵐ m (⟦ Γ ˢ⟧□ n ⟦Γ⟧ m , c))
        >>= (λ l ⟦A⟧ → ⟦ D ⟧ᵐ l (⟦ Γ ˢ⟧□ n ⟦Γ⟧ l , ⟦A⟧))
    ≡⟨ cong (λ x -> x >>= _) (sym (bind-to->>= Γ (⟪ ⟦ E₁ ⟧ₘ , ⟦ E₂ ⟧ₘ ⟫)
                (handle ⟦ C₁ ⟧ᵐ ⟦ C₂ ⟧ᵐ ⟦ C₃ ⟧ᵐ) n ⟦Γ⟧)) ⟩
        bindEvent Γ (⟪ ⟦ E₁ ⟧ₘ , ⟦ E₂ ⟧ₘ ⟫)
            (handle ⟦ C₁ ⟧ᵐ ⟦ C₂ ⟧ᵐ ⟦ C₃ ⟧ᵐ) n ⟦Γ⟧
        >>= (λ l ⟦A⟧ → ⟦ D ⟧ᵐ l (⟦ Γ ˢ⟧□ n ⟦Γ⟧ l , ⟦A⟧))
    ≡⟨ sym (bind-to->>= Γ (bindEvent Γ (⟪_,_⟫ ⟦ E₁ ⟧ₘ ⟦ E₂ ⟧ₘ) (handle ⟦ C₁ ⟧ᵐ ⟦ C₂ ⟧ᵐ ⟦ C₃ ⟧ᵐ))
                    ⟦ D ⟧ᵐ n ⟦Γ⟧) ⟩
        bindEvent Γ (bindEvent Γ ⟪ ⟦ E₁ ⟧ₘ , ⟦ E₂ ⟧ₘ ⟫ (handle ⟦ C₁ ⟧ᵐ ⟦ C₂ ⟧ᵐ ⟦ C₃ ⟧ᵐ)) ⟦ D ⟧ᵐ n ⟦Γ⟧
    ∎
    where
    lemma : ∀ m c
           -> handle
               ⟦ ⟨ C₁ /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) ⟧ᵐ
               ⟦ ⟨ C₂ /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) ⟧ᵐ
               ⟦ ⟨ C₃ /⟩ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) ⟧ᵐ m (⟦ Γ ˢ⟧□ n ⟦Γ⟧ m , c)
            ≡ (handle ⟦ C₁ ⟧ᵐ ⟦ C₂ ⟧ᵐ ⟦ C₃ ⟧ᵐ m (⟦ Γ ˢ⟧□ n ⟦Γ⟧ m , c)
                >>= λ l ⟦A⟧ → ⟦ D ⟧ᵐ l (⟦ Γ ˢ⟧□ n ⟦Γ⟧ l , ⟦A⟧))
    lemma m (inj₁ (inj₁ (⟦A⟧ , ⟦◇B⟧)))
        rewrite subst″-sound C₁ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) {m} {(⟦ Γ ˢ⟧□ n ⟦Γ⟧ m , ⟦A⟧) , ⟦◇B⟧}
              | bind-to->>= (Γ ˢ ,, G now ,, Event H now) ⟦ C₁ ⟧ᵐ ⟦ substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D ⟧ᵐ m ((⟦ Γ ˢ⟧□ n ⟦Γ⟧ m , ⟦A⟧) , ⟦◇B⟧)
              | (ext λ l → ext λ ⟦C⟧ → subst″-sound-lemma Γ n m l D ⟦Γ⟧ ⟦C⟧)
        = refl
    lemma m (inj₁ (inj₂ (⟦◇A⟧ , ⟦B⟧)))
        rewrite subst″-sound C₂ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) {m} {(⟦ Γ ˢ⟧□ n ⟦Γ⟧ m , ⟦◇A⟧) , ⟦B⟧}
              | bind-to->>= (Γ ˢ ,, Event G now ,, H now) ⟦ C₂ ⟧ᵐ ⟦ substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D ⟧ᵐ m ((⟦ Γ ˢ⟧□ n ⟦Γ⟧ m , ⟦◇A⟧) , ⟦B⟧)
              | (ext λ l → ext λ ⟦C⟧ → subst″-sound-lemma Γ n m l D ⟦Γ⟧ ⟦C⟧)
        = refl
    lemma m (inj₂ (⟦A⟧ , ⟦B⟧))
        rewrite subst″-sound C₃ (substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D) {m} {(⟦ Γ ˢ⟧□ n ⟦Γ⟧ m , ⟦A⟧) , ⟦B⟧}
              | bind-to->>= (Γ ˢ ,, G now ,, H now) ⟦ C₃ ⟧ᵐ ⟦ substitute′ ((Γ ˢˢₛ 𝒯erm) ↑ 𝒯erm) D ⟧ᵐ m ((⟦ Γ ˢ⟧□ n ⟦Γ⟧ m , ⟦A⟧) , ⟦B⟧)
              | (ext λ l → ext λ ⟦C⟧ → subst″-sound-lemma Γ n m l D ⟦Γ⟧ ⟦C⟧)
        = refl
