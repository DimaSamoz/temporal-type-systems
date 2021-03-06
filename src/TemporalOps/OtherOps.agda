
module TemporalOps.OtherOps where

open import CategoryTheory.Instances.Reactive
open import CategoryTheory.Functor
open import CategoryTheory.Monad
open import CategoryTheory.Comonad
open import CategoryTheory.NatTrans
open import CategoryTheory.BCCCs
open import CategoryTheory.CartesianStrength

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

open import Holes.Term using (⌞_⌟)
open import Holes.Cong.Propositional

open Monad M-◇
open Comonad W-□
private module F-◇ = Functor F-◇
private module F-□ = Functor F-□
open ≡.≡-Reasoning


-- | Natural transformations between modalities

-- delay A by 1 is the same as ▹ A
▹¹-to-▹ : F-delay 1 ⟺ F-▹
▹¹-to-▹ = record
    { to   = record { at = λ A n x → x ; nat-cond = refl }
    ; from = record { at = λ A n x → x ; nat-cond = refl }
    ; iso1 = refl
    ; iso2 = refl
    }

-- □ A is always available, in particular, after a delay by k
□-to-▹ᵏ : ∀(k : ℕ) -> F-□ ⟹ F-delay k
□-to-▹ᵏ k = record
    { at = at-□-▹ᵏ k
    ; nat-cond = nat-cond-□-▹ᵏ k
    }
    where
    at-□-▹ᵏ : ∀(k : ℕ)(A : τ) -> □ A ⇴ delay A by k
    at-□-▹ᵏ zero A n a = a n
    at-□-▹ᵏ (suc k) A zero a = top.tt
    at-□-▹ᵏ (suc k) A (suc n) a = at-□-▹ᵏ k A n a

    nat-cond-□-▹ᵏ : ∀(k : ℕ){A B : τ} {f : A ⇴ B} →
      Functor.fmap (F-delay k) f ∘ at-□-▹ᵏ k A ≈
      at-□-▹ᵏ k B ∘ Functor.fmap F-□ f
    nat-cond-□-▹ᵏ zero {A} {B} {f} {n} {a} = refl
    nat-cond-□-▹ᵏ (suc k) {A} {B} {f} {zero} {a} = refl
    nat-cond-□-▹ᵏ (suc k) {A} {B} {f} {suc n} {a} = nat-cond-□-▹ᵏ k

-- If A is delayed by k, then it is delayed
▹ᵏ-to-◇ : ∀(k : ℕ) -> F-delay k ⟹ F-◇
▹ᵏ-to-◇ k = record
    { at = λ A n a → k , a
    ; nat-cond = refl
    }

-- □ A is always available, in particular, after any delay
□-to-◇ : ∀{k} -> F-□ ⟹ F-◇
□-to-◇ {k} = ▹ᵏ-to-◇ k ⊚ □-to-▹ᵏ k


-- | Monadic operations for ◇


return : ∀{A : τ} -> A ⇴ ◇ A
return {A} = η.at A

-- Monadic extension
_⋆ : ∀{A B : τ} -> (A ⇴ ◇ B) -> (◇ A ⇴ ◇ B)
_⋆ {A} {B} f = μ.at B ∘ F-◇.fmap f
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
        μ.at C n ⌞ (((fmap g ∘ μ.at B) ∘ fmap f) n a) ⌟
    ≡⟨ cong! (≈-cong-left {f = fmap g} (μ.nat-cond {B} {◇ C} {g} {n} {fmap f n a}) {n} {a >>= f}) ⟩
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

-- Return is left unit to bind
>>=-unit-left : ∀{A B : τ}{n : ℕ} -> (a : A n)(f : A ⇴ ◇ B)
             -> (η.at A n a) >>= f ≡ f n a
>>=-unit-left a f = η-unit1

-- Return is right unit to bind
>>=-unit-right : ∀{A : τ}{n : ℕ} -> (a : (◇ A) n)
              -> a >>= η.at A ≡ a
>>=-unit-right a = η-unit2
