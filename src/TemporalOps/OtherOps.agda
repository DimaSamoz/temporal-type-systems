
module TemporalOps.OtherOps where

open import CategoryTheory.Instances.Reactive
open import CategoryTheory.Functor
open import CategoryTheory.Monad
open import CategoryTheory.Comonad
open import CategoryTheory.NatTrans

open import TemporalOps.Next
open import TemporalOps.Delay
open import TemporalOps.Diamond
open import TemporalOps.Box
open import TemporalOps.Common.Other

open import Relation.Binary.PropositionalEquality as ≡
open import Data.Product
open import Data.Sum
open import Data.Nat hiding (_*_)
open import Data.Nat.Properties
            using (+-identityʳ ; +-comm ; +-suc ; +-assoc)

open Monad M-◇
open Comonad W-□
private module F-◇ = Functor F-◇
private module F-□ = Functor F-◇
open ≡.≡-Reasoning



-- | Monadic operations for ◇


return : ∀{A : τ} -> A ⇴ ◇ A
return {A} = η.at A

-- Monadic extension
_⋆ : ∀{A B : τ} -> (A ⇴ ◇ B) -> (◇ A ⇴ ◇ B)
_⋆ {A} {B} f n a = μ.at B n (F-◇.fmap f n a)
infixl 55 _⋆

-- Bind operator
_>>=_ : ∀{A B : τ}{n : ℕ} -> (◇ A) n -> (A ⇴ (◇ B)) -> (◇ B) n
_>>=_ {n = n} a f = (f ⋆) n a

-- Bind is associative
>>=-assoc : ∀{A B C : τ}{n : ℕ} -> (a : (◇ A) n) -> (f : (A ⇴ (◇ B))) -> (g : (B ⇴ (◇ C)))
         -> (a >>= f) >>= g ≡ a >>= (λ k x → (f k x) >>= g)
>>=-assoc {A}{B}{C} {n} a f g =
    begin
        ((a >>= f) >>= g)
    ≡⟨⟩
        μ.at C n (((fmap g ∘ μ.at B) ∘ fmap f) n a)
    ≡⟨ cong (μ.at C n) (≈-cong-left {f = fmap g} (μ.nat-cond {B} {◇ C} {g} {n} {fmap f n a}) {n} {a >>= f}) ⟩
        (((μ.at C ∘ μ.at (◇ C)) ∘ fmap (fmap g)) ∘ fmap f) n a
    ≡⟨ lemma ⟩
        (((μ.at C ∘ fmap (μ.at C)) ∘ fmap (fmap g)) ∘ fmap f) n a
    ≡⟨ cong (μ.at C n) (≈-cong-left {f = fmap g} (sym (fmap-∘ {a = fmap f n a})) {n} {a >>= f}) ⟩
        μ.at C n ((fmap (μ.at C ∘ fmap g) ∘ fmap f) n a)
    ≡⟨ cong (μ.at C n) (sym (fmap-∘ {a = a})) ⟩
        μ.at C n (fmap ((μ.at C ∘ fmap g) ∘ f) n a)
    ≡⟨⟩
        (a >>= (λ k x → f k x >>= g))
    ∎
    where
    open Functor F-◇
    lemma : (((μ.at C ∘ μ.at (◇ C)) ∘ fmap (fmap g)) ∘ fmap f) n a
          ≡ (((μ.at C ∘ fmap (μ.at C)) ∘ fmap (fmap g)) ∘ fmap f) n a
    lemma rewrite μ-assoc {C} {n} {((fmap (fmap g)) ∘ fmap f) n a} = refl

-- Return is right unit to bind
>>=-unit-right : ∀{A : τ}{n : ℕ} -> (a : (◇ A) n)
         -> a >>= η.at A ≡ a
>>=-unit-right a = η-unit2

-- | Other properties of ◇

-- ◇ is a □-strong monad
◇-□-strong : ∀{A B : τ} -> □ A ⊗ ◇ B ⇴ ◇ (□ A ⊗ B)
◇-□-strong {A} n (□A , (k , v)) =
    k , (pair-delay k n (_⟹_.at (□-to-▹ᵏ k) (□ A) n (δ.at A n □A) , v))

-- Sample a signal at an event
◇-sample : ∀{A B : τ} -> □ A ⊗ ◇ B ⇴ ◇ (A ⊗ B)
◇-sample {A} = F-□.fmap (ε.at A * id) ∘ ◇-□-strong

-- If we know that A and B eventually happens, then at a future point either
--   * A happens and B still hasn't
--   * B happens but A still hasn't
--   * A and B happen at the same time
-- This is expressed as the sum of the three possibilities
◇-select : ∀{A B : τ} -> (◇ A ⊗ ◇ B) ⇴ ◇ ((A ⊗ ◇ B) ⊕ (◇ A ⊗ B) ⊕ (A ⊗ B))
◇-select n ((k₁ , v₁) , (k₂ , v₂)) with compare k₁ k₂
◇-select {A} {B} n ((k₁ , v₁) , .(suc (k₁ + l)) , v₂) | less .k₁ l  =
    k₁ , sum-delay k₁ n (inj₁ (sum-delay k₁ n
                        (inj₁ (pair-delay-◇ k₁ (suc l) n (v₁ , v₂′)))))
    where
    v₂′ : delay B by (k₁ + suc l) at n
    v₂′ rewrite +-suc k₁ l = v₂
    pair-delay-◇ : ∀{A B : τ} -> (k l : ℕ) -> (delay A by k ⊗ delay B by (k + l))
                                   ⇴ delay (A ⊗ ◇ B) by k
    pair-delay-◇ zero l n (dA , dB) = dA , (l , dB)
    pair-delay-◇ (suc k) l n p = Functor.fmap F-▹ (pair-delay-◇ k l) n (pair-▹ n p)
◇-select {A} {B} n ((.(suc (k₂ + l)) , v₁) , k₂ , v₂)  | greater .k₂ l =
    k₂ , sum-delay k₂ n (inj₁ (sum-delay k₂ n
                        (inj₂ (pair-delay-◇ k₂ (suc l) n (v₁′ , v₂)))))
    where
    v₁′ : delay A by (k₂ + suc l) at n
    v₁′ rewrite +-suc k₂ l = v₁
    pair-delay-◇ : ∀{A B : τ} -> (k l : ℕ) -> (delay A by (k + l) ⊗ delay B by k)
                                   ⇴ delay (◇ A ⊗ B) by k
    pair-delay-◇ zero l n (dA , dB) = (l , dA) , dB
    pair-delay-◇ (suc k) l n p = Functor.fmap F-▹ (pair-delay-◇ k l) n (pair-▹ n p)

◇-select n ((k₁ , v₁)              , .k₁ , v₂) | equal .k₁ =
    k₁ , sum-delay k₁ n (inj₂ (pair-delay k₁ n (v₁ , v₂)))
