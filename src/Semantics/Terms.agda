
{- Denotational semantics of the terms in the category of temporal types. -}
module Semantics.Terms where

open import Syntax.Context renaming (_,_ to _,,_)
open import Syntax.Terms
open import Syntax.Types
open import Semantics.Types
open import Semantics.Context
open import CategoryTheory.Instances.Reactive
open import TemporalOps.Box
open import TemporalOps.Diamond
open import CategoryTheory.Functor
open import CategoryTheory.NatTrans
import CategoryTheory.Monad as M
import CategoryTheory.Comonad as W

open import Data.Product
open import Data.Sum
open import Data.Nat as N

open W.Comonad W-□
open M.Monad M-◇
private module ε = _⟹_ ε
private module η = _⟹_ η
private module μ = _⟹_ μ

mutual
    -- Denotation of pure terms as morphisms from contexts to types.
    ⟦_⟧ₘ : ∀{Γ A} -> Γ ⊢ A -> (⟦ Γ ⟧ₓ ⇴ ⟦ A ⟧ⱼ)
    ⟦ var _∈_.top ⟧ₘ n (⟦Γ⟧ , ⟦A⟧) = ⟦A⟧
    ⟦ (var (pop {B = B now}    x)) ⟧ₘ n (⟦Γ⟧ , _) = ⟦ var x ⟧ₘ n ⟦Γ⟧
    ⟦ (var (pop {B = B always} x)) ⟧ₘ n (⟦Γ⟧ , _) = ⟦ var x ⟧ₘ n ⟦Γ⟧
    ⟦ lam M ⟧ₘ n env = λ ⟦A⟧ → ⟦ M ⟧ₘ n (env , ⟦A⟧)
    ⟦ F $ M ⟧ₘ n env = ⟦ F ⟧ₘ n env (⟦ M ⟧ₘ n env)
    ⟦ unit ⟧ₘ n env = top.tt
    ⟦ [ M ,, N ] ⟧ₘ n env = ⟦ M ⟧ₘ n env , ⟦ N ⟧ₘ n env
    ⟦ fst M ⟧ₘ n env = proj₁ (⟦ M ⟧ₘ n env)
    ⟦ snd M ⟧ₘ n env = proj₂ (⟦ M ⟧ₘ n env)
    ⟦ inl M ⟧ₘ n env = inj₁ (⟦ M ⟧ₘ n env)
    ⟦ inr M ⟧ₘ n env = inj₂ (⟦ M ⟧ₘ n env)
    ⟦ case M inl↦ B₁ ||inr↦ B₂ ⟧ₘ n env with ⟦ M ⟧ₘ n env
    ⟦ case M inl↦ B₁ ||inr↦ B₂ ⟧ₘ n env | inj₁ x = ⟦ lam B₁ ⟧ₘ n env x
    ⟦ case M inl↦ B₁ ||inr↦ B₂ ⟧ₘ n env | inj₂ y = ⟦ lam B₂ ⟧ₘ n env y
    ⟦ svar _∈_.top ⟧ₘ n (⟦Γ⟧ , ⟦A⟧) = ⟦A⟧
    ⟦ svar (pop {B = B now} x) ⟧ₘ n (⟦Γ⟧ , ⟦A⟧) = ⟦ svar x ⟧ₘ n ⟦Γ⟧
    ⟦ svar (pop {B = B always} x) ⟧ₘ n (⟦Γ⟧ , ⟦A⟧) = ⟦ svar x ⟧ₘ n ⟦Γ⟧
    ⟦ present S ⟧ₘ n env = ⟦ S ⟧ₘ n env n
    ⟦_⟧ₘ {Γ} (stable S) n env = λ k → ⟦ S ⟧ₘ k (⟦ Γ ⟧ˢₓ n env k)
    ⟦ sig S ⟧ₘ n env = ⟦ S ⟧ₘ n env
    ⟦ letSig S In B ⟧ₘ n env = ⟦ B ⟧ₘ n (env , ⟦ S ⟧ₘ n env)
    ⟦ event E ⟧ₘ n env = ⟦ E ⟧ᵐ n env


    -- Denotation of computational terms as Kleisli morphisms from contexts to types.
    ⟦_⟧ᵐ : ∀{Γ A} -> Γ ⊨ A -> (⟦ Γ ⟧ₓ ⇴ ◇ ⟦ A ⟧ⱼ)
    ⟦_⟧ᵐ {A = A} (pure M) n env = η.at ⟦ A ⟧ⱼ n (⟦ M ⟧ₘ n env)
    ⟦ letSig S InC C ⟧ᵐ n env = ⟦ C ⟧ᵐ n (env , (⟦ S ⟧ₘ n env n))
    ⟦_⟧ᵐ {Γ} (letEvt_In_ {A = A} {B} E C) n env = ⟦◇A⟧ >>= ⟦A=>◇B⟧
            where
            ⟦◇A⟧ : (◇ ⟦ A ⟧ₜ) n
            ⟦◇A⟧ = ⟦ E ⟧ₘ n env
            ⟦A=>◇B⟧ : ⟦ A ⟧ₜ ⇴ (◇ ⟦ B ⟧ₜ)
            ⟦A=>◇B⟧ k ⟦A⟧ = ⟦ C ⟧ᵐ k (top.tt , ⟦A⟧)
    ⟦ select_↦_||_↦_||both↦_ {A = A} {B} {C} E₁ C₁ E₂ C₂ C₃ ⟧ᵐ n env =
        ◇-select n (⟦ E₁ ⟧ₘ n env , ⟦ E₂ ⟧ₘ n env) >>= ⟦select⟧
        where
        -- Handle all three possibilities of event ordering by selecting
        -- the correct continuation
        ⟦select⟧ :  (  ⟦ A ⟧ₜ ⊗ ◇ ⟦ B ⟧ₜ)
                 ⊕ (◇ ⟦ A ⟧ₜ ⊗   ⟦ B ⟧ₜ)
                 ⊕ (  ⟦ A ⟧ₜ ⊗   ⟦ B ⟧ₜ) ⇴ ◇ ⟦ C ⟧ₜ
        ⟦select⟧ n (inj₁ (inj₁ (⟦A⟧ , ⟦◇B⟧))) = ⟦ C₁ ⟧ᵐ n ((top.tt , ⟦◇B⟧) , ⟦A⟧)
        ⟦select⟧ n (inj₁ (inj₂ (⟦◇A⟧ , ⟦B⟧))) = ⟦ C₂ ⟧ᵐ n ((top.tt , ⟦◇A⟧) , ⟦B⟧)
        ⟦select⟧ n (inj₂ (⟦A⟧ , ⟦B⟧))         = ⟦ C₃ ⟧ᵐ n ((top.tt , ⟦A⟧)  , ⟦B⟧)
