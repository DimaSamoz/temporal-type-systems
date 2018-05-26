{-# OPTIONS --allow-unsolved-metas #-}
module Semantics.Bind where

open import Syntax.Types
open import Syntax.Context renaming (_,_ to _,,_)
open import Syntax.Terms
open import Syntax.Substitution.Kits
open import Syntax.Substitution.Instances
open import Syntax.Substitution.Lemmas

open import Semantics.Types
open import Semantics.Terms
open import Semantics.Context
open import Semantics.Substitution.Kits
open import Semantics.Substitution.Traversal
open import Semantics.Substitution.Instances

open import CategoryTheory.Categories using (Category ; ext)
open import CategoryTheory.Functor
open import CategoryTheory.NatTrans
open import CategoryTheory.Monad
open import CategoryTheory.Comonad
open import CategoryTheory.CartesianStrength
open import CategoryTheory.Instances.Reactive renaming (top to ⊤)
open import TemporalOps.Diamond
open import TemporalOps.Delay
open import TemporalOps.Box
open import TemporalOps.OtherOps
open import TemporalOps.StrongMonad

open import Data.Sum
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as ≡
    using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; subst)

open ≡.≡-Reasoning
open import Holes.Term using (⌞_⌟)
open import Holes.Cong.Propositional

open Comonad W-□
open Monad M-◇
private module F-◇ = Functor F-◇
private module F-□ = Functor F-□
open Functor F-□ renaming (fmap to □-f)
open Functor F-◇ renaming (fmap to ◇-f)
private module ▹ᵏ-C k = CartesianFunctor (F-cart-delay k)
private module ▹ᵏ-F k = Functor (F-delay k)
private module □-▹ᵏ k = _⟹_ (□-to-▹ᵏ k)


bind-to->>= : ∀ Γ {⟦A⟧ ⟦B⟧} -> (⟦E⟧ : ⟦ Γ ⟧ₓ ⇴ ◇ ⟦A⟧) (⟦C⟧ : ⟦ Γ ˢ ⟧ₓ ⊗ ⟦A⟧ ⇴ ◇ ⟦B⟧)
        -> (n : ℕ) (⟦Γ⟧ : ⟦ Γ ⟧ₓ n)
        -> bindEvent Γ ⟦E⟧ ⟦C⟧ n ⟦Γ⟧
        ≡ (⟦E⟧ n ⟦Γ⟧ >>= λ l ⟦A⟧ → ⟦C⟧ l (⟦ Γ ˢ⟧□ n ⟦Γ⟧ l , ⟦A⟧))
bind-to->>= Γ {⟦A⟧} {⟦B⟧} ⟦E⟧ ⟦C⟧ n ⟦Γ⟧ =
    begin
        bindEvent Γ ⟦E⟧ ⟦C⟧ n ⟦Γ⟧
    ≡⟨⟩
        μ.at ⟦B⟧ n (F-◇.fmap (⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id) n (st ⟦ Γ ˢ ⟧ₓ ⟦A⟧ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ⟦E⟧ n ⟦Γ⟧)))
    ≡⟨ cong (μ.at ⟦B⟧ n) (lemma (⟦E⟧ n ⟦Γ⟧)) ⟩
        μ.at ⟦B⟧ n (F-◇.fmap (⟦C⟧ ∘ ⟨ (λ l _ → ⟦ Γ ˢ⟧□ n ⟦Γ⟧ l) , id ⟩) n (⟦E⟧ n ⟦Γ⟧))
    ≡⟨⟩
        (⟦E⟧ n ⟦Γ⟧ >>= (λ l ⟦A⟧ → ⟦C⟧ l (⟦ Γ ˢ⟧□ n ⟦Γ⟧ l , ⟦A⟧)))
    ∎
    where
    lemma : ∀ ◇⟦A⟧
         -> F-◇.fmap (⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id) n (st ⟦ Γ ˢ ⟧ₓ ⟦A⟧ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , ◇⟦A⟧))
          ≡ F-◇.fmap (⟦C⟧ ∘ ⟨ (λ l _ → ⟦ Γ ˢ⟧□ n ⟦Γ⟧ l) , id ⟩) n ◇⟦A⟧
    lemma (k , a) =
        begin
            F-◇.fmap (⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id) n (st ⟦ Γ ˢ ⟧ₓ ⟦A⟧ n (⟦ Γ ˢ⟧□ n ⟦Γ⟧ , (k , a)))
        ≡⟨⟩
            k , ▹ᵏ-F.fmap k (⟦C⟧ ∘ ε.at ⟦ Γ ˢ ⟧ₓ * id) n
                (▹ᵏ-C.m k (□ ⟦ Γ ˢ ⟧ₓ) ⟦A⟧ n (□-▹ᵏ.at k (□ ⟦ Γ ˢ ⟧ₓ) n (δ.at ⟦ Γ ˢ ⟧ₓ k (⟦ Γ ˢ⟧□ n ⟦Γ⟧)) , a))
        ≡⟨ {!   !} ⟩
            k , ▹ᵏ-F.fmap k (⟦C⟧ ∘ ⟨ (λ l _ → ⟦ Γ ˢ⟧□ n ⟦Γ⟧ l) , id ⟩) n a
        ≡⟨⟩
            F-◇.fmap (⟦C⟧ ∘ ⟨ (λ l _ → ⟦ Γ ˢ⟧□ n ⟦Γ⟧ l) , id ⟩) n (k , a)
        ∎
