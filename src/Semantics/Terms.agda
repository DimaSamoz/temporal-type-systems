
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
    ⟦_⟧ₘ : ∀{Γ Δ A} -> Δ ⁏ Γ ⊢ A -> (⟦ Δ ⁏ Γ ⟧ₑ ⇴ ⟦ A ⟧ₜ)
    ⟦ var _∈_.top ⟧ₘ n (⟦Δ⟧ , (⟦Γ⟧ , ⟦A⟧)) = ⟦A⟧
    ⟦_⟧ₘ {Γ} {Δ} (var (pop x)) n (⟦Δ⟧ , (⟦Γ⟧ , _)) = ⟦ var {_} {Δ} x ⟧ₘ n (⟦Δ⟧ , ⟦Γ⟧)
    ⟦ lam M      ⟧ₘ n (⟦Δ⟧ , ⟦Γ⟧) ⟦A⟧ = ⟦ M ⟧ₘ n (⟦Δ⟧ , (⟦Γ⟧ , ⟦A⟧))
    ⟦ F $ M      ⟧ₘ n env     = ⟦ F ⟧ₘ n env (⟦ M ⟧ₘ n env)
    ⟦ unit       ⟧ₘ n env     = top.tt
    ⟦ [ M ,, N ] ⟧ₘ n env     = ⟦ M ⟧ₘ n env , ⟦ N ⟧ₘ n env
    ⟦ fst M      ⟧ₘ n env     = proj₁ (⟦ M ⟧ₘ n env)
    ⟦ snd M      ⟧ₘ n env     = proj₂ (⟦ M ⟧ₘ n env)
    ⟦ inl M      ⟧ₘ n env     = inj₁ (⟦ M ⟧ₘ n env)
    ⟦ inr M      ⟧ₘ n env     = inj₂ (⟦ M ⟧ₘ n env)
    ⟦ case S inl↦ M₁ ||inr↦ M₂ ⟧ₘ n env with ⟦ S ⟧ₘ n env
    ⟦ case S inl↦ M₁ ||inr↦ M₂ ⟧ₘ n env | inj₁ x = ⟦ lam M₁ ⟧ₘ n env x
    ⟦ case S inl↦ M₁ ||inr↦ M₂ ⟧ₘ n env | inj₂ y = ⟦ lam M₂ ⟧ₘ n env y
    ⟦_⟧ₘ {Γ} {Δ} (svar _∈_.top) n ((⟦Δ⟧ , ⟦U⟧) , ⟦Γ⟧) = ⟦U⟧ n
    ⟦_⟧ₘ {Γ} {Δ} (svar (pop x)) n ((⟦Δ⟧ ,  _) , ⟦Γ⟧) = ⟦ svar {Γ} x ⟧ₘ n (⟦Δ⟧ n , ⟦Γ⟧)
    ⟦_⟧ₘ {Γ} {Δ} (sig M) n (⟦Δ⟧ , ⟦Γ⟧) k = ⟦ M ⟧ₘ k (stable Δ ⟦Δ⟧ k , top.tt)
    ⟦_⟧ₘ {Γ} {Δ} (letSig_In_ {A = A} S M) n (⟦Δ⟧ , ⟦Γ⟧) = ⟦ M ⟧ₘ n ((stable Δ ⟦Δ⟧ , ⟦S⟧) , ⟦Γ⟧)
            where
            -- Denotation of the bound signal term
            ⟦SigS⟧ : (□ ⟦ A ⟧ₜ) n
            ⟦SigS⟧ = ⟦ S ⟧ₘ n (⟦Δ⟧ , ⟦Γ⟧)
            -- S is a signal, so its underlying type is constant at all times
            ⟦S⟧ : ∀ k -> ⟦ A ⟧ₜ k
            ⟦S⟧ k = ε.at ⟦ A ⟧ₜ k ⟦SigS⟧
    ⟦ event {A = A} E ⟧ₘ n env = ⟦ E ⟧ᵐ n env


    -- Denotation of computational terms as Kleisli morphisms from contexts to types.
    ⟦_⟧ᵐ : ∀{Γ Δ A} -> Δ ⁏ Γ ⊨ A -> (⟦ Δ ⁏ Γ ⟧ₑ ⇴ ◇ ⟦ A ⟧ₜ)
    ⟦_⟧ᵐ {Γ} {Δ} {A} (pure M) n env = η.at ⟦ A ⟧ₜ n (⟦ M ⟧ₘ n env)
    ⟦_⟧ᵐ {Γ} {Δ} (letSig_InC_ {A = A} S M) n (⟦Δ⟧ , ⟦Γ⟧) = ⟦ M ⟧ᵐ n ((stable Δ ⟦Δ⟧ , ⟦S⟧) , ⟦Γ⟧)
            where
            -- S is a signal, so its underlying type is constant at all times
            ⟦S⟧ : ∀ k -> ⟦ A ⟧ₜ k
            ⟦S⟧ k = ε.at ⟦ A ⟧ₜ k (⟦ S ⟧ₘ n (⟦Δ⟧ , ⟦Γ⟧))
    ⟦_⟧ᵐ {Γ} {Δ} {B} (letEvt_In_ {A = A} E C) n (⟦Δ⟧ , ⟦Γ⟧) = ⟦EvtA⟧ >>= ⟦A=>EvtB⟧
            where
            ⟦EvtA⟧ : (◇ ⟦ A ⟧ₜ) n
            ⟦EvtA⟧ = ⟦ E ⟧ₘ n (⟦Δ⟧ , ⟦Γ⟧)
            ⟦A=>EvtB⟧ : ⟦ A ⟧ₜ ⇴ (◇ ⟦ B ⟧ₜ)
            ⟦A=>EvtB⟧ k x = ⟦ C ⟧ᵐ k ((stable Δ ⟦Δ⟧ k) , (top.tt , x))
    ⟦ select E₁ ↦ C₁ || E₂ ↦ C₂ ||both↦ C₃ ⟧ᵐ n env with ⟦ E₁ ⟧ₘ n env | ⟦ E₂ ⟧ₘ n env
    ⟦ select E₁ ↦ C₁ || E₂ ↦ C₂ ||both↦ C₃ ⟧ᵐ n env | e₁ | e₂ with N.compare (proj₁ e₁) (proj₁ e₂)
    -- k₂ = suc (k₁ + l) -- k₁ happens first
    ⟦_⟧ᵐ {Γ} {Δ} {C} (select_↦_||_↦_||both↦_ {A = A} {B} E₁ C₁ E₂ C₂ C₃) n (⟦Δ⟧ , ⟦Γ⟧) | e₁@(k₁ , v₁) | e₂@(.(suc (k₁ N.+ l)) , v₂) | less .k₁ l = e₁ -⊗- e₂ >>= ⟦A⟧⊗⟦B⟧=>⟦EvtC⟧
            where
            ⟦A⟧⊗⟦B⟧=>⟦EvtC⟧ : (⟦ A ⟧ₜ ⊗ ⟦ B ⟧ₜ) ⇴ (◇ ⟦ C ⟧ₜ)
            ⟦A⟧⊗⟦B⟧=>⟦EvtC⟧ k (a , b) = ⟦ C₁ ⟧ᵐ k ((stable Δ ⟦Δ⟧ k) , ((top.tt , η.at ⟦ B ⟧ₜ k b) , a))
    -- k₁ = suc (k₂ + l)  -- k₂ happens first
    ⟦_⟧ᵐ {Γ} {Δ} {C} (select_↦_||_↦_||both↦_ {A = A} {B} E₁ C₁ E₂ C₂ C₃) n (⟦Δ⟧ , ⟦Γ⟧) | e₁@(.(suc (k₂ N.+ l)) , v₁) | e₂@(k₂ , v₂) | greater .k₂ l = e₁ -⊗- e₂ >>= ⟦A⟧⊗⟦B⟧=>⟦EvtC⟧
            where
            ⟦A⟧⊗⟦B⟧=>⟦EvtC⟧ : (⟦ A ⟧ₜ ⊗ ⟦ B ⟧ₜ) ⇴ (◇ ⟦ C ⟧ₜ)
            ⟦A⟧⊗⟦B⟧=>⟦EvtC⟧ k (a , b) = ⟦ C₂ ⟧ᵐ k (stable Δ ⟦Δ⟧ k , (top.tt , η.at ⟦ A ⟧ₜ k a) , b)
    -- k₁ = k₂ -- Both happen at the same time
    ⟦_⟧ᵐ {Γ} {Δ} {C} (select_↦_||_↦_||both↦_ {A = A} {B} E₁ C₁ E₂ C₂ C₃) n (⟦Δ⟧ , ⟦Γ⟧) | e₁@(k₁ , v₁) | e₂@(.k₁ , v₂) | equal .k₁ = e₁ -⊗- e₂ >>= ⟦A⟧⊗⟦B⟧=>⟦EvtC⟧
            where
            ⟦A⟧⊗⟦B⟧=>⟦EvtC⟧ : (⟦ A ⟧ₜ ⊗ ⟦ B ⟧ₜ) ⇴ (◇ ⟦ C ⟧ₜ)
            ⟦A⟧⊗⟦B⟧=>⟦EvtC⟧ k (a , b) = ⟦ C₃ ⟧ᵐ k (stable Δ ⟦Δ⟧ k , (top.tt , a) , b)
