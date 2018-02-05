
{- Delay operator. -}
module TemporalOps.Delay where

open import CategoryTheory.Categories
open import CategoryTheory.Functor
open import TemporalOps.Common
open import TemporalOps.Next

open import Data.Nat.Properties using (+-identityʳ ; +-comm)
open import Relation.Binary.HeterogeneousEquality
    using (_≅_ ; ≅-to-≡ ; ≡-to-≅ ; ≅-to-type-≡ ; ≅-to-subst-≡)
import Relation.Binary.PropositionalEquality as ≡
open Category ℝeactive

-- General iteration
-- iter f n v = fⁿ(v)
iter : (τ -> τ) -> ℕ -> τ -> τ
iter F zero    A = A
iter F (suc n) A = F (iter F n A)

-- Multi-step delay
delay_by_ : τ -> ℕ -> τ
delay A by zero = A
delay A by suc n = ▹ (delay A by n)
infix 67 delay_by_

-- || Lemmas for the delay operator

-- Extra delay is cancelled out by extra waiting.
delay-plus : ∀{A} -> (n l k : ℕ)
          -> delay A by (n + l) at (n + k) ≡ delay A by l at k
delay-plus zero l k = refl
delay-plus (suc n) = delay-plus n

-- || Derived lemmas - they can all be expressed in terms of delay-plus,
-- || but they are given explicitly for simplicity.

-- Delay by n is cancelled out by waiting n extra steps.
delay-plus-left0 : ∀{A} -> (n k : ℕ)
              -> delay A by n at (n + k) ≡ A at k
delay-plus-left0 zero k = refl
delay-plus-left0 (suc n) k = delay-plus-left0 n k

-- Delay-plus-left0 can be converted to delay-plus (heterogeneously).
delay-plus-left0-eq : ∀{A : τ} -> (n l : ℕ)
                   -> (v : delay A by n at (n + l))
                   -> (v′ : delay A by (n + 0) at (n + l))
                   -> (p : v ≅ v′)
                   -> rew (delay-plus-left0 {A} n l) v
                    ≅ rew (delay-plus {A} n 0 l) v′
delay-plus-left0-eq zero l v v′ p = p
delay-plus-left0-eq (suc n) l v v′ p = delay-plus-left0-eq n l v v′ p

-- Extra delay by n steps is cancelled out by waiting for n steps.
delay-plus-right0 : ∀{A} -> (n l : ℕ)
              -> delay A by (n + l) at n ≡ delay A by l at 0
delay-plus-right0 zero l = refl
delay-plus-right0 (suc n) l = delay-plus-right0 n l

-- Delaying by n is the same as delaying by (n + 0)
delay-plus-zero : ∀{A} -> (n k : ℕ)
              -> delay A by n at k ≡ delay A by (n + 0) at k
delay-plus-zero {A} n k rewrite +-identityʳ n = refl

-- Functor instance for delay
instance
    F-delay : ℕ -> Endofunctor ℝeactive
    F-delay k = record
        { omap = delay_by k
        ; fmap = fmap-delay k
        ; fmap-id = λ {_ n a} -> fmap-delay-id k {_} {n} {a}
        ; fmap-∘ = fmap-delay-∘ k
        ; fmap-cong = fmap-delay-cong k
        }
        where
        -- Lifting of delay
        fmap-delay : {A B : τ} -> (k : ℕ) -> A ⇴ B -> delay A by k ⇴ delay B by k
        fmap-delay zero    f = f
        fmap-delay (suc k) f = Functor.fmap F-▹ (fmap-delay k f)
        -- Delay preserves identities
        fmap-delay-id : ∀ (k : ℕ) {A : τ} {n : ℕ} {a : (delay A by k) n}
                 -> (fmap-delay k id at n) a ≡ a
        fmap-delay-id zero = refl
        fmap-delay-id (suc k) {A} {zero} = refl
        fmap-delay-id (suc k) {A} {suc n} = fmap-delay-id k {A} {n}
        -- Delay preserves composition
        fmap-delay-∘ : ∀ (k : ℕ) {A B C : τ} {g : B ⇴ C} {f : A ⇴ B} {n : ℕ} {a : (delay A by k) n}
                -> (fmap-delay k (g ∘ f) at n) a ≡ (fmap-delay k g ∘ fmap-delay k f at n) a
        fmap-delay-∘ zero = refl
        fmap-delay-∘ (suc k) {n = zero} = refl
        fmap-delay-∘ (suc k) {n = suc n} = fmap-delay-∘ k {n = n}
        -- Delay is congruent
        fmap-delay-cong : ∀ (k : ℕ) {A B : τ} {f f′ : A ⇴ B}
                -> ({n : ℕ} {a : A at n} -> f n a ≡ f′ n a)
                -> ({n : ℕ} {a : delay A by k at n}
                    -> (fmap-delay k f at n) a
                     ≡ (fmap-delay k f′ at n) a)
        fmap-delay-cong zero e = e
        fmap-delay-cong (suc k) e {zero} = refl
        fmap-delay-cong (suc k) e {suc n} = fmap-delay-cong k e

-- || Lemmas for the interaction of fmap and delay-plus

-- Lifted version of the delay-plus lemma
-- Arguments have different types, so we need heterogeneous equality
fmap-delay-plus : ∀ {A B : τ} {f : A ⇴ B} (n k l : ℕ)
               -> (v : delay A by (n + k) at (n + l)) (v′ : delay A by k at l)
               -> v ≅ v′
               -> (Functor.fmap (F-delay (n + k)) f at (n + l)) v
                ≅ (Functor.fmap (F-delay      k)  f at      l)  v′
fmap-delay-plus zero    k l v .v _≅_.refl = _≅_.refl
fmap-delay-plus (suc n) k l v  v′ pf       = fmap-delay-plus n k l v v′ pf


-- Specialised version with v of type delay A by (n + k) at (n + l)
-- Uses explicit rewrites and homogeneous equality
fmap-delay-plus-n+k : ∀ {A B : τ} {f : A ⇴ B} (n k l : ℕ)
               -> (v : delay A by (n + k) at (n + l))
               -> rew (delay-plus n k l) ((Functor.fmap (F-delay (n + k)) f at (n + l)) v)
                ≡ (Functor.fmap (F-delay k) f at l) (rew (delay-plus n k l) v)
fmap-delay-plus-n+k {A} n k l v =
    ≅-to-rew-≡ (fmap-delay-plus n k l v v′ v≅v′) (delay-plus n k l)
    where
    v′ : delay A by k at l
    v′ = rew (delay-plus n k l) v
    v≅v′ : v ≅ v′
    v≅v′ = rew-to-≅ (delay-plus n k l)

-- Specialised version with v of type delay A by k at l
-- Uses explicit rewrites and homogeneous equality
fmap-delay-plus-k : ∀ {A B : τ} {f : A ⇴ B} (n k l : ℕ) (v : delay A by k at l)
               -> Functor.fmap (F-delay (n + k)) f (n + l) (rew (sym (delay-plus n k l)) v)
                ≡ rew (sym (delay-plus n k l)) (Functor.fmap (F-delay k) f l v)
fmap-delay-plus-k {A} {B} {f} n k l v =
    sym (≅-to-rew-≡ (≅.sym (fmap-delay-plus n k l v′ v v≅v′)) (sym (delay-plus n k l)))
    where
    private module ≅ = Relation.Binary.HeterogeneousEquality
    v′ : delay A by (n + k) at (n + l)
    v′ = rew (sym (delay-plus n k l)) v
    v≅v′ : v′ ≅ v
    v≅v′ = ≅.sym (rew-to-≅ (sym (delay-plus n k l)))
