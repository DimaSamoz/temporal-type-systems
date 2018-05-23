{-# OPTIONS --allow-unsolved-metas #-}

module TemporalOps.Linear where

open import CategoryTheory.Instances.Reactive
open import CategoryTheory.Functor
open import CategoryTheory.CartesianStrength
open import CategoryTheory.NatTrans
open import CategoryTheory.Monad
open import CategoryTheory.Linear

open import TemporalOps.Next
open import TemporalOps.Delay
open import TemporalOps.Diamond
open import TemporalOps.OtherOps
open import TemporalOps.Common.Other
open import TemporalOps.Common.Compare
open import TemporalOps.Common.Rewriting

open import Data.Product
open import Data.Product.Properties
open import Data.Sum
open import Data.Nat hiding (_*_)
open import Data.Nat.Properties
            using (+-identityʳ ; +-comm ; +-suc ; +-assoc)

open import Relation.Binary.PropositionalEquality hiding (inspect)

open import Holes.Term using (⌞_⌟)
open import Holes.Cong.Propositional

open ≡-Reasoning

open L ℝeactive-BCCC M-◇

ℝeactive-linear : Linear ℝeactive-BCCC M-◇
ℝeactive-linear = record
    { linprod = λ A B →
    record { ⟪_,_⟫ = prod-◇
           ; *π₁-comm = λ {C} {l₁} {l₂} {n} {a} →
                        *π₁-comm-◇ {A}{B}{C} {l₁} {l₂} {n} {a}
           ; *π₂-comm = {!   !}
           ; ⊛-unique = {!   !}
           }
    }
    where
    open Functor F-▹
    open Functor F-◇ renaming (fmap to ◇-f)
    private module ▹ᵏ-F k = Functor (F-delay k)
    private module ▹ᵏ-◇ k = _⟹_ (▹ᵏ-to-◇ k)
    private module ▹ᵏ-C k = CartesianFunctor (F-cart-delay k)
    open Monad M-◇
    open CartesianFunctor F-cart-▹ renaming (m to m-▹)


    pair-delay-◇₁ : ∀{A B : τ} -> (k l : ℕ) -> (delay A by suc (k + l) ⊗ delay B by k)
                                   ⇴ delay (◇ A ⊗ B) by k
    pair-delay-◇₁ zero l n (dA , dB) = (suc l , dA) , dB
    pair-delay-◇₁ {A}{B} (suc k) l n p = fmap (pair-delay-◇₁ k l) n
        (m-▹ (delay A by suc (k + l)) (delay B by k) n p)

    pair-delay-◇₂ : ∀{A B : τ} -> (k l : ℕ) -> (delay A by k ⊗ delay B by suc (k + l))
                                   ⇴ delay (A ⊗ ◇ B) by k
    pair-delay-◇₂ zero l n (dA , dB) = dA , (suc l , dB)
    pair-delay-◇₂ {A}{B} (suc k) l n p = fmap (pair-delay-◇₂ k l) n
        (m-▹ (delay A by k) (delay B by suc (k + l)) n p)

    prod-◇-compare : ∀{A B : τ} -> (k₁ k₂ n : ℕ)
                  -> (a₁ : delay A by k₁ at n)(a₂ : delay B by k₂ at n)
                  -> Ordering k₁ k₂ -> ◇ (A ⊛ B) at n
    prod-◇-compare {A} {B} k₁ .(suc (k₁ + l)) n a₁ a₂ (less .k₁ l) =
        k₁ , ▹ᵏ-F.fmap k₁ ι₁ n (▹ᵏ-F.fmap k₁ ι₁ n (pair-delay-◇₂ k₁ l n (a₁ , a₂)))
    prod-◇-compare {A} {B} .(suc (k₂ + l)) k₂ n a₁ a₂ (greater .k₂ l) =
        k₂ , ▹ᵏ-F.fmap k₂ ι₁ n (▹ᵏ-F.fmap k₂ ι₂ n (pair-delay-◇₁ k₂ l n (a₁ , a₂)))
    prod-◇-compare {A} {B} k₁ .k₁ n a₁ a₂ (equal .k₁) =
        k₁ , ▹ᵏ-F.fmap k₁ ι₂ n (▹ᵏ-C.m k₁ A B n (a₁ , a₂))

    ◇-select : ∀{A B : τ} -> (◇ A ⊗ ◇ B) ⇴ ◇ (A ⊛ B)
    ◇-select {A}{B} n ((k₁ , a₁) , (k₂ , a₂)) =
        prod-◇-compare {A}{B} k₁ k₂ n a₁ a₂ (compare k₁ k₂)

    prod-◇ : ∀{A B L : τ} -> (L ⇴ ◇ A) -> (L ⇴ ◇ B) -> (L ⇴ ◇ (A ⊛ B))
    prod-◇ fa fb n lp = ◇-select n (fa n lp , fb n lp)

    *π₁-comm-◇ : ∀{A B L} -> {l₁ : L ⇴ ◇ A} {l₂ : L ⇴ ◇ B}
           -> (μ.at A ∘ ◇-f *π₁) ∘ (prod-◇ l₁ l₂) ≈ l₁
    *π₁-comm-◇ {A}{B}{L}{l₁}{l₂} {n} {a} with inspect (l₁ n a , l₂ n a)
    *π₁-comm-◇ | ((k₁ , a₁) , (k₂ , a₂)) with≡ pf with inspect (compare k₁ k₂)
    *π₁-comm-◇ {A}{B}{L}{l₁}{l₂}{n}{a} | ((k₁ , a₁) , .(suc (k₁ + l)) , a₂) with≡ pf
                                           | less .k₁ l with≡ cpf =
        begin
            (μ.at A n (◇-f *π₁ n (◇-select n ⌞ (l₁ n a , l₂ n a) ⌟)))
        ≡⟨ cong! pf ⟩
            μ.at A n (◇-f *π₁ n
                (prod-◇-compare k₁ (suc (k₁ + l)) n a₁ a₂ (⌞ compare k₁ (suc (k₁ + l)) ⌟)))
        ≡⟨ cong! cpf ⟩
            μ.at A n (◇-f *π₁ n
                (prod-◇-compare k₁ (suc (k₁ + l)) n a₁ a₂ (less k₁ l)))
        ≡⟨⟩
            μ.at A n (k₁ ,
                ▹ᵏ-F.fmap k₁ *π₁ n ⌞ (▹ᵏ-F.fmap k₁ ι₁ n (▹ᵏ-F.fmap k₁ ι₁ n
                    (pair-delay-◇₂ k₁ l n (a₁ , a₂)))) ⌟)
        ≡⟨ cong! (▹ᵏ-F.fmap-∘ k₁ {g = ι₁ {A ⊗ ◇ B ⊕ ◇ A ⊗ B} {A ⊗ B}}
                                    {ι₁ {A ⊗ ◇ B} {◇ A ⊗ B}}{n} {pair-delay-◇₂ k₁ l n (a₁ , a₂)}) ⟩
            μ.at A n (k₁ ,
                ⌞ ▹ᵏ-F.fmap k₁ *π₁ n (▹ᵏ-F.fmap k₁ (ι₁ ∘ ι₁) n
                    (pair-delay-◇₂ k₁ l n (a₁ , a₂))) ⌟)
        ≡⟨ cong! (▹ᵏ-F.fmap-∘ k₁ {g = *π₁} {ι₁ ∘ ι₁} {n} {pair-delay-◇₂ k₁ l n (a₁ , a₂)}) ⟩
            μ.at A n (k₁ ,
                ▹ᵏ-F.fmap k₁ ([ η.at A ∘ π₁ ⁏ π₁ {B = L} ⁏ η.at A ∘ π₁ {B = L} ] ∘ ι₁ ∘ ι₁) n
                    (pair-delay-◇₂ k₁ l n (a₁ , a₂)))
        ≡⟨⟩
            μ.at A n (k₁ ,
                ⌞ ▹ᵏ-F.fmap k₁ (η.at A ∘ π₁) n
                    (pair-delay-◇₂ k₁ l n (a₁ , a₂)) ⌟)
        ≡⟨ cong! (▹ᵏ-F.fmap-∘ k₁) ⟩
            μ.at A n (k₁ , ▹ᵏ-F.fmap k₁ (η.at A) n
                ⌞ ▹ᵏ-F.fmap k₁ π₁ n (pair-delay-◇₂ k₁ l n (a₁ , a₂)) ⌟)
        ≡⟨ cong! (lemma k₁ l {n} {a₁ , a₂}) ⟩
            μ.at A n (k₁ , ▹ᵏ-F.fmap k₁ (η.at A) n a₁)
        ≡⟨ η-unit2 ⟩
            k₁ , a₁
        ≡⟨ sym (,-injectiveˡ pf) ⟩
            l₁ n a
        ∎
        where
        lemma : ∀ (k l : ℕ) -> ▹ᵏ-F.fmap k π₁ ∘ pair-delay-◇₂ k l ≈ π₁
        lemma zero l = refl
        lemma (suc k) l {zero} = refl
        lemma (suc k) l {suc n} = lemma k l {n}

    *π₁-comm-◇ {A}{B}{L}{l₁}{l₂}{n}{a} | ((.(suc (k₂ + l)) , a₁) , k₂ , a₂) with≡ pf
                                      | greater .k₂ l  with≡ cpf  =
        begin
            (μ.at A n (◇-f *π₁ n (◇-select n ⌞ (l₁ n a , l₂ n a) ⌟)))
        ≡⟨ cong! pf ⟩
            μ.at A n (◇-f *π₁ n
                (prod-◇-compare (suc (k₂ + l)) k₂ n a₁ a₂ (⌞ compare (suc (k₂ + l)) k₂ ⌟)))
        ≡⟨ cong! cpf ⟩
            μ.at A n (◇-f *π₁ n
                (prod-◇-compare (suc (k₂ + l)) k₂ n a₁ a₂ (greater k₂ l)))
        ≡⟨⟩
            μ.at A n (k₂ ,
                ▹ᵏ-F.fmap k₂ *π₁ n ⌞ (▹ᵏ-F.fmap k₂ ι₁ n (▹ᵏ-F.fmap k₂ ι₂ n
                    (pair-delay-◇₁ k₂ l n (a₁ , a₂)))) ⌟)
        ≡⟨ cong! (▹ᵏ-F.fmap-∘ k₂ {g = ι₁ {A ⊗ ◇ B ⊕ ◇ A ⊗ B} {A ⊗ B}}
                                    {ι₂ {A ⊗ ◇ B} {◇ A ⊗ B}}{n} {pair-delay-◇₁ k₂ l n (a₁ , a₂)}) ⟩
            μ.at A n (k₂ ,
                ⌞ ▹ᵏ-F.fmap k₂ *π₁ n (▹ᵏ-F.fmap k₂ (ι₁ ∘ ι₂) n
                    (pair-delay-◇₁ k₂ l n (a₁ , a₂))) ⌟)
        ≡⟨ cong! (▹ᵏ-F.fmap-∘ k₂ {g = *π₁} {ι₁ ∘ ι₂} {n} {pair-delay-◇₁ k₂ l n (a₁ , a₂)}) ⟩
            μ.at A n (k₂ ,
                ▹ᵏ-F.fmap k₂ ([ η.at A ∘ π₁ {B = L} ⁏ π₁ {B = B} ⁏ η.at A ∘ π₁ {B = L} ] ∘ ι₁ ∘ ι₂) n
                    (pair-delay-◇₁ k₂ l n (a₁ , a₂)))
        ≡⟨⟩
            μ.at A n (k₂ , ⌞ ▹ᵏ-F.fmap k₂ π₁ n (pair-delay-◇₁ k₂ l n (a₁ , a₂)) ⌟)
        ≡⟨ refl ⟩
            μ.at A n (◇-f π₁ n (k₂ , pair-delay-◇₁ k₂ l n (a₁ , a₂)))
        ≡⟨ {!   !} ⟩
        -- ≡⟨ cong! (lemma k₂ l {n} {a₁ , a₂}) ⟩
        --     μ.at A n (k₂ , ▹ᵏ-F.fmap k₂ (▹ᵏ-◇.at (suc l) A) n (split-▹ᵏ k₂ l n a₁))
            suc (k₂ + l) , a₁
        ≡⟨ sym (,-injectiveˡ pf) ⟩
            l₁ n a
        ∎
        where
        split-▹ᵏ : ∀ {A} k l -> delay A by suc (k + l) ⇴ delay (delay A by suc l) by k
        split-▹ᵏ zero l n a = a
        split-▹ᵏ (suc k) l zero a = top.tt
        split-▹ᵏ (suc k) l (suc n) a = split-▹ᵏ k l n a

        lemma : ∀ {A B} (k l  : ℕ)
             -> ▹ᵏ-F.fmap k (π₁ {B = B}) ∘ pair-delay-◇₁ {A} k l
              ≈ ▹ᵏ-F.fmap k (▹ᵏ-◇.at (suc l) A) ∘ split-▹ᵏ k l ∘ π₁
        lemma zero l {n} = refl
        lemma (suc k) l {zero} = refl
        lemma (suc k) l {suc n} = lemma k l

        lemma2 : ∀ {A B} k l n (a₁ : delay A by suc (k + l) at n)
                               (a₂ : delay B by k at n)
              -> μ.at A n (◇-f π₁ n (k , pair-delay-◇₁ k l n (a₁ , a₂)))
               ≡ (suc (k + l) , a₁)
        lemma2 zero l n a₁ a₂ = refl
        lemma2 (suc k) l zero a₁ a₂ = {!   !}
        lemma2 (suc k) l (suc n) a₁ a₂ = {!   !}


    *π₁-comm-◇ {l₁ = l₁} {l₂} {n} {a} | ((k₁ , a₁) , .k₁ , a₂) with≡ pf
                                      | equal .k₁  with≡ cpf = {!   !}
