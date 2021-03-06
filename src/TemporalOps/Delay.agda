
{- Delay operator. -}
module TemporalOps.Delay where

open import CategoryTheory.Categories
open import CategoryTheory.Instances.Reactive
open import CategoryTheory.Functor
open import CategoryTheory.CartesianStrength
open import TemporalOps.Common
open import TemporalOps.Next

open import Data.Nat.Properties using (+-identityʳ ; +-comm ; +-assoc ; +-suc)
open import Relation.Binary.HeterogeneousEquality as ≅ using (_≅_ ; ≅-to-≡)
import Relation.Binary.PropositionalEquality as ≡
open import Data.Product
open import Data.Sum


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
delay-+ : ∀{A} -> (n l k : ℕ)
          -> delay A by (n + l) at (n + k) ≡ delay A by l at k
delay-+ zero l k = refl
delay-+ (suc n) = delay-+ n

-- || Derived lemmas - they can all be expressed in terms of delay-+,
-- || but they are given explicitly for simplicity.

-- Delay by n is cancelled out by waiting n extra steps.
delay-+-left0 : ∀{A} -> (n k : ℕ)
              -> delay A by n at (n + k) ≡ A at k
delay-+-left0 zero k = refl
delay-+-left0 (suc n) k = delay-+-left0 n k

-- delay-+-left0 can be converted to delay-+ (heterogeneously).
delay-+-left0-eq : ∀{A : τ} -> (n l : ℕ)
                -> Proof-≡ (delay-+-left0 {A} n l) (delay-+ {A} n 0 l)
delay-+-left0-eq zero l v v′ pf = ≅-to-≡ pf
delay-+-left0-eq (suc n) l = delay-+-left0-eq n l

-- Extra delay by n steps is cancelled out by waiting for n steps.
delay-+-right0 : ∀{A} -> (n l : ℕ)
              -> delay A by (n + l) at n ≡ delay A by l at 0
delay-+-right0 zero l = refl
delay-+-right0 (suc n) l = delay-+-right0 n l

-- Delaying by n is the same as delaying by (n + 0)
delay-+0-left : ∀{A} -> (k n : ℕ)
             -> delay A by k at n ≡ delay A by (k + 0) at n
delay-+0-left {A} k n rewrite +-identityʳ k = refl

-- If the delay is greater than the wait amount, we get unit
delay-⊤ : ∀{A} -> (n k : ℕ)
       -> ⊤ at n ≡ delay A by (n + suc k) at n
delay-⊤ {A} n k = sym (delay-+-right0 n (suc k))

-- Associativity of arguments in the delay lemma
delay-assoc-sym : ∀{A} (n k l j : ℕ)
               -> Proof-≅ (sym (delay-+ {A} n (k + l) (k + j)))
                          (sym (delay-+ {A} (n + k) l j))
delay-assoc-sym zero zero l j v v′ pr = pr
delay-assoc-sym zero (suc k) l j = delay-assoc-sym zero k l j
delay-assoc-sym (suc n) k l j = delay-assoc-sym n k l j


-- Functor instance for delay
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

-- || Lemmas for the interaction of fmap and delay-+

-- Lifted version of the delay-+ lemma
-- Arguments have different types, so we need heterogeneous equality
fmap-delay-+ : ∀ {A B : τ} {f : A ⇴ B} (n k l : ℕ)
            -> Fun-≅ (Functor.fmap (F-delay (n + k)) f at (n + l))
                     (Functor.fmap (F-delay      k)  f at      l)
fmap-delay-+ zero    k l v .v ≅.refl = ≅.refl
fmap-delay-+ (suc n) k l v  v′ pf       = fmap-delay-+ n k l v v′ pf


-- Specialised version with v of type delay A by (n + k) at (n + l)
-- Uses explicit rewrites and homogeneous equality
fmap-delay-+-n+k : ∀ {A B : τ} {f : A ⇴ B} (n k l : ℕ)
               -> (v : delay A by (n + k) at (n + l))
               -> rew (delay-+ n k l) ((Functor.fmap (F-delay (n + k)) f at (n + l)) v)
                ≡ (Functor.fmap (F-delay k) f at l) (rew (delay-+ n k l) v)
fmap-delay-+-n+k {A} n k l v =
    ≅-to-rew-≡ (fmap-delay-+ n k l v v′ v≅v′) (delay-+ n k l)
    where
    v′ : delay A by k at l
    v′ = rew (delay-+ n k l) v
    v≅v′ : v ≅ v′
    v≅v′ = rew-to-≅ (delay-+ n k l)

-- Lifted delay lemma with delay-+-left0
fmap-delay-+-n+0 : ∀ {A B : τ} {f : A ⇴ B} (n l : ℕ)
               -> {v : delay A by n at (n + l)}
               -> rew (delay-+-left0 n l) ((Functor.fmap (F-delay n) f at (n + l)) v)
                ≡ f l (rew (delay-+-left0 n l) v)
fmap-delay-+-n+0 {A} zero l = refl
fmap-delay-+-n+0 {A} (suc n) l = fmap-delay-+-n+0 n l

-- Specialised version with v of type delay A by k at l
-- Uses explicit rewrites and homogeneous equality
fmap-delay-+-k : ∀ {A B : τ} {f : A ⇴ B} (n k l : ℕ)
              ->(v : delay A by k at l)
              -> Functor.fmap (F-delay (n + k)) f (n + l) (rew (sym (delay-+ n k l)) v)
               ≡ rew (sym (delay-+ n k l)) (Functor.fmap (F-delay k) f l v)
fmap-delay-+-k {A} {B} {f} n k l v =
    sym (≅-to-rew-≡ (≅.sym (fmap-delay-+ n k l v′ v v≅v′)) (sym (delay-+ n k l)))
    where
    v′ : delay A by (n + k) at (n + l)
    v′ = rew (sym (delay-+ n k l)) v
    v≅v′ : v′ ≅ v
    v≅v′ = ≅.sym (rew-to-≅ (sym (delay-+ n k l)))


-- Delay is a Cartesian functor
F-cart-delay : ∀ k -> CartesianFunctor (F-delay k) ℝeactive-cart ℝeactive-cart
F-cart-delay k = record
    { u = u-delay k
    ; m = m-delay k
    ; m-nat₁ = m-nat₁-delay k
    ; m-nat₂ = m-nat₂-delay k
    ; associative = assoc-delay k
    ; unital-right = unit-right-delay k
    ; unital-left = λ {B} {n} {a} -> unit-left-delay k {B} {n} {a}
    }
    where
    open CartesianFunctor F-cart-▹

    u-delay : ∀ k -> ⊤ ⇴ delay ⊤ by k
    u-delay zero = λ n _ → top.tt
    u-delay (suc k) zero top.tt = top.tt
    u-delay (suc k) (suc n) top.tt = u-delay k n top.tt

    m-delay : ∀ k (A B : τ) -> (delay A by k ⊗ delay B by k) ⇴ delay (A ⊗ B) by k
    m-delay zero A B = λ n x → x
    m-delay (suc k) A B = Functor.fmap F-▹ (m-delay k A B) ∘ m (delay A by k) (delay B by k)

    m-nat₁-delay : ∀ k {A B C : τ} (f : A ⇴ B)
          -> Functor.fmap (F-delay k) (f * id) ∘ m-delay k A C
           ≈ m-delay k B C ∘ Functor.fmap (F-delay k) f * id
    m-nat₁-delay zero f = refl
    m-nat₁-delay (suc k) f {zero} = refl
    m-nat₁-delay (suc k) f {suc n} = m-nat₁-delay k f

    m-nat₂-delay : ∀ k {A B C : τ} (f : A ⇴ B)
          -> Functor.fmap (F-delay k) (id * f) ∘ m-delay k C A
           ≈ m-delay k C B ∘ id * Functor.fmap (F-delay k) f
    m-nat₂-delay zero f = refl
    m-nat₂-delay (suc k) f {zero} = refl
    m-nat₂-delay (suc k) f {suc n} = m-nat₂-delay k f

    assoc-delay : ∀ k {A B C : τ}
           -> m-delay k A (B ⊗ C) ∘ id * m-delay k B C ∘ assoc-right
            ≈ Functor.fmap (F-delay k) assoc-right ∘ m-delay k (A ⊗ B) C ∘ m-delay k A B * id
    assoc-delay zero = refl
    assoc-delay (suc k) {A} {B} {C} {zero} = refl
    assoc-delay (suc k) {A} {B} {C} {suc n} = assoc-delay k

    unit-right-delay : ∀ k {A : τ} ->
        Functor.fmap (F-delay k) unit-right ∘ m-delay k A ⊤ ∘ (id * u-delay k) ≈ unit-right
    unit-right-delay zero {A} {n} = refl
    unit-right-delay (suc k) {A} {zero} = refl
    unit-right-delay (suc k) {A} {suc n} = unit-right-delay k

    unit-left-delay : ∀ k {B : τ} ->
        Functor.fmap (F-delay k) unit-left ∘ m-delay k ⊤ B ∘ (u-delay k * id) ≈ unit-left
    unit-left-delay zero = refl
    unit-left-delay (suc k) {B} {zero} = refl
    unit-left-delay (suc k) {B} {suc n} = unit-left-delay k

m-delay-+-n+0 : ∀ {A B} k l {a b}
      -> (rew (delay-+-left0 k l)
          (CartesianFunctor.m (F-cart-delay k) A B (k + l) (a , b)))
       ≡ (rew (delay-+-left0 k l) a , rew (delay-+-left0 k l) b)
m-delay-+-n+0 zero l = refl
m-delay-+-n+0 (suc k) l = m-delay-+-n+0 k l

m-delay-+-sym : ∀ {A B} k l m{a b}
      -> rew (sym (delay-+ k m l))
            (CartesianFunctor.m (F-cart-delay m) A B l (a , b))
       ≡ CartesianFunctor.m (F-cart-delay (k + m)) A B (k + l)
            ((rew (sym (delay-+ k m l)) a) , (rew (sym (delay-+ k m l)) b))
m-delay-+-sym zero l m = refl
m-delay-+-sym (suc k) l m = m-delay-+-sym k l m
