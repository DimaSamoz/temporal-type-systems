
{- Denotational semantics of the terms in the category of temporal types. -}
module Semantics.Terms where

open import Syntax.Context renaming (_,_ to _,,_)
open import Syntax.Terms
open import Syntax.Types

open import Semantics.Types
open import Semantics.Context
open import Semantics.Select

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
    ⟦ var (pop x) ⟧ₘ n (⟦Γ⟧ , _) = ⟦ var x ⟧ₘ n ⟦Γ⟧
    ⟦ lam M ⟧ₘ n env = λ ⟦A⟧ → ⟦ M ⟧ₘ n (env , ⟦A⟧)
    ⟦ F $ M ⟧ₘ n env = ⟦ F ⟧ₘ n env (⟦ M ⟧ₘ n env)
    ⟦ unit ⟧ₘ n env = top.tt
    ⟦ [ M ,, N ] ⟧ₘ n env = ⟦ M ⟧ₘ n env , ⟦ N ⟧ₘ n env
    ⟦ fst M ⟧ₘ n env = proj₁ (⟦ M ⟧ₘ n env)
    ⟦ snd M ⟧ₘ n env = proj₂ (⟦ M ⟧ₘ n env)
    ⟦ inl M ⟧ₘ n env = inj₁ (⟦ M ⟧ₘ n env)
    ⟦ inr M ⟧ₘ n env = inj₂ (⟦ M ⟧ₘ n env)
    ⟦ case M inl↦ B₁ ||inr↦ B₂ ⟧ₘ n env with ⟦ M ⟧ₘ n env
    ⟦ case M inl↦ B₁ ||inr↦ B₂ ⟧ₘ n env | inj₁ x = ⟦ B₁ ⟧ₘ n (env , x)
    ⟦ case M inl↦ B₁ ||inr↦ B₂ ⟧ₘ n env | inj₂ y = ⟦ B₂ ⟧ₘ n (env , y)
    ⟦ svar _∈_.top ⟧ₘ n (⟦Γ⟧ , ⟦A⟧) = ⟦A⟧
    ⟦ svar (pop x) ⟧ₘ n (⟦Γ⟧ , _) = ⟦ svar x ⟧ₘ n ⟦Γ⟧
    ⟦ sample S ⟧ₘ n env = ⟦ S ⟧ₘ n env n
    ⟦ stable {Γ} S ⟧ₘ n env = λ k → ⟦ S ⟧ₘ k (⟦ Γ ⟧ˢₓ n env k)
    ⟦ sig S ⟧ₘ n env = ⟦ S ⟧ₘ n env
    ⟦ letSig S In B ⟧ₘ n env = ⟦ B ⟧ₘ n (env , ⟦ S ⟧ₘ n env)
    ⟦ event E ⟧ₘ n env = ⟦ E ⟧ᵐ n env


    -- Denotation of computational terms as Kleisli morphisms from contexts to types.
    ⟦_⟧ᵐ : ∀{Γ A} -> Γ ⊨ A -> (⟦ Γ ⟧ₓ ⇴ ◇ ⟦ A ⟧ⱼ)
    ⟦_⟧ᵐ {A = A} (pure M) n env = η.at ⟦ A ⟧ⱼ n (⟦ M ⟧ₘ n env)
    ⟦ letSig S InC C ⟧ᵐ n env = ⟦ C ⟧ᵐ n (env , (⟦ S ⟧ₘ n env))
    ⟦ letEvt_In_ {Γ} {A} E C ⟧ᵐ n env =
        ⟦ E ⟧ₘ n env >>= λ k ⟦A⟧ → ⟦ C ⟧ᵐ k (⟦ Γ ⟧ˢₓ n env k , ⟦A⟧)
    ⟦ select_↦_||_↦_||both↦_ {Γ} {A} {B} {C} E₁ C₁ E₂ C₂ C₃ ⟧ᵐ n env =
        ◇-select n (⟦ E₁ ⟧ₘ n env , ⟦ E₂ ⟧ₘ n env)
        >>= ⟦select⟧ Γ A B C n env ⟦ C₁ ⟧ᵐ ⟦ C₂ ⟧ᵐ ⟦ C₃ ⟧ᵐ
