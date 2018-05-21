
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

-- | Other properties of ◇

-- ◇ is a □-strong monad
-- ◇-□-strong : ∀{A B : τ} -> □ A ⊗ ◇ B ⇴ ◇ (□ A ⊗ B)
-- ◇-□-strong {A} n (□A , (k , v)) =
--     k , (pair-delay k n (_⟹_.at (□-to-▹ᵏ k) (□ A) n (δ.at A n □A) , v))

-- Sample a signal at an event
-- ◇-sample : ∀{A B : τ} -> □ A ⊗ ◇ B ⇴ ◇ (A ⊗ B)
-- ◇-sample {A} = F-◇.fmap (ε.at A * id) ∘ ◇-□-strong

◇-□-Strong : WStrongMonad ℝeactive-cart M-◇ W-cart-□
◇-□-Strong = record
    { st = st-◇
    ; st-nat₁ = st-nat₁-◇
    ; st-nat₂ = st-nat₂-◇
    ; st-λ = st-λ-◇
    ; st-α = st-α-◇
    ; st-η = {!   !}
    ; st-μ = {!   !}
    }
    where
    open Functor F-◇ renaming (fmap to ◇-f ; omap to ◇-o)
    open Functor F-□ renaming (fmap to □-f ; omap to □-o)
    private module ▹ᵏ-C k = CartesianFunctor (F-cart-delay k)
    private module ▹ᵏ-F k = Functor (F-delay k)
    private module ▹-F = Functor F-▹
    private module ▹-C = CartesianFunctor (F-cart-▹)
    private module □-C = CartesianFunctor (F-cart-□)
    private module □-CW = CartesianComonad (W-cart-□)
    private module □-▹ᵏ k = _⟹_ (□-to-▹ᵏ k)

    st-◇ : ∀(A B : τ) -> □ A ⊗ ◇ B ⇴ ◇ (□ A ⊗ B)
    st-◇ A B n (□A , (k , a)) = k , ▹ᵏ-C.m k (□ A) B n (□-▹ᵏ.at k (□ A) n (δ.at A k □A) , a)

    st-nat₁-◇ : ∀{A B C : τ} (f : A ⇴ B)
             -> ◇-f (□-f f * id) ∘ st-◇ A C ≈ st-◇ B C ∘ □-f f * id
    st-nat₁-◇ {A} {B} {C} f {n} {□A , k , a}
        rewrite ▹ᵏ-C.m-nat₁ k (□-f f)
                {n} {(□-▹ᵏ.at k (□ A) n (δ.at A k □A)) , a}
              | (□-▹ᵏ.nat-cond k {□ A} {□ B} {□-f f} {n} {δ.at A k □A})
        = refl

    st-nat₂-◇ : ∀{A B C : τ} (f : A ⇴ B)
             -> ◇-f (id * f) ∘ st-◇ C A ≈ st-◇ C B ∘ id * ◇-f f
    st-nat₂-◇ {A} {B} {C} f {n} {□C , k , a}
        rewrite ▹ᵏ-C.m-nat₂ k f {n} {□-▹ᵏ.at k (□ C) n (δ.at C k □C) , a} = refl

    st-λ-◇ : ∀{A} -> ◇-f π₂ ∘ st-◇ ⊤ A ≈ π₂
    st-λ-◇ {A} {n} {□⊤ , (k , a)} =
        begin
            ◇-f π₂ n (st-◇ ⊤ A n (□⊤ , (k , a)))
        ≡⟨⟩
            ◇-f π₂ n (k , ▹ᵏ-C.m k (□ ⊤) A n (□-▹ᵏ.at k (□ ⊤) n (δ.at ⊤ n □⊤) , a))
        ≡⟨⟩
            k , ▹ᵏ-F.fmap k π₂ n (▹ᵏ-C.m k (□ ⊤) A n (□-▹ᵏ.at k (□ ⊤) n (δ.at ⊤ n □⊤) , a))
        ≡⟨ cong (λ x -> k , x) lemma ⟩
            k , a
        ∎
        where
        lemma : ▹ᵏ-F.fmap k π₂ ∘ ▹ᵏ-C.m k (□ ⊤) A ≈ π₂
        lemma {n} {t , b} =
            begin
                ▹ᵏ-F.fmap k π₂ n (▹ᵏ-C.m k (□ ⊤) A n (t , b))
            ≡⟨⟩
                ▹ᵏ-F.fmap k π₂ n (▹ᵏ-C.m k (□ ⊤) A n (⌞ t ⌟ , b))
            ≡⟨ cong! (▹ᵏ-F.fmap-id k {□ ⊤}{n}{t}) ⟩
                ▹ᵏ-F.fmap k π₂ n (▹ᵏ-C.m k (□ ⊤) A n (▹ᵏ-F.fmap k ⌞ id ⌟ n t , b))
            ≡⟨⟩
                ▹ᵏ-F.fmap k π₂ n (▹ᵏ-C.m k (□ ⊤) A n (⌞ ▹ᵏ-F.fmap k (u ∘ ε.at ⊤) n t ⌟ , b))
            ≡⟨ cong! (▹ᵏ-F.fmap-∘ k) ⟩
                ▹ᵏ-F.fmap k π₂ n (▹ᵏ-C.m k (□ ⊤) A n (▹ᵏ-F.fmap k u n (▹ᵏ-F.fmap k (ε.at ⊤) n t) , b))
            ≡⟨ cong (▹ᵏ-F.fmap k π₂ n) (sym (▹ᵏ-C.m-nat₁ k u)) ⟩
                ▹ᵏ-F.fmap k π₂ n (▹ᵏ-F.fmap k (u * id) n (▹ᵏ-C.m k ⊤ A n (▹ᵏ-F.fmap k (ε.at ⊤) n t , b)))
            ≡⟨ sym (▹ᵏ-F.fmap-∘ k) ⟩
                ▹ᵏ-F.fmap k (π₂ ∘ u * id) n (▹ᵏ-C.m k ⊤ A n (▹ᵏ-F.fmap k (ε.at ⊤) n t , b))
            ≡⟨⟩
                ▹ᵏ-F.fmap k π₂ n (▹ᵏ-C.m k ⊤ A n (⌞ ▹ᵏ-F.fmap k (ε.at ⊤) n t ⌟ , b))
            ≡⟨ cong! (⊤-eq k n t) ⟩
                ▹ᵏ-F.fmap k π₂ n (▹ᵏ-C.m k ⊤ A n (▹ᵏ-C.u k n top.tt , b))
            ≡⟨ ▹ᵏ-C.unital-left k ⟩
                b
            ∎
            where
            ⊤-eq : ∀ k n t -> ▹ᵏ-F.fmap k (ε.at ⊤) n t ≡ ▹ᵏ-C.u k n top.tt
            ⊤-eq zero n t = refl
            ⊤-eq (suc k) zero t = refl
            ⊤-eq (suc k) (suc n) t = ⊤-eq k n t

    st-α-◇ : ∀{A B C : τ}
          -> st-◇ A (□ B ⊗ C) ∘ id * st-◇ B C ∘ assoc-right ∘ m⁻¹ A B * id
           ≈ ◇-f (assoc-right ∘ m⁻¹ A B * id) ∘ st-◇ (A ⊗ B) C
    st-α-◇ {A} {B} {C} {n} {□A⊗B , (zero , a)} = refl
    st-α-◇ {A} {B} {C} {zero} {□A⊗B , (suc k , a)} = refl
    st-α-◇ {A} {B} {C} {suc n} {□A⊗B , (suc k , a)} =
        begin
            st-◇ A (□ B ⊗ C) (suc n)
                (□-f π₁ (suc n) □A⊗B , st-◇ B C (suc n) (□-f π₂ (suc n) □A⊗B , ((suc k) , a)))
        ≡⟨ cong (λ x → (suc k) , x) (
            begin
                ▹ᵏ-C.m k (□ A) (□ B ⊗ C) n
                    ( □-▹ᵏ.at k (□ A) n (δ.at A k (□-f π₁ n □A⊗B))
                    , ▹ᵏ-C.m k (□ B) C n (□-▹ᵏ.at k (□ B) n (δ.at B n (□-f π₂ n □A⊗B)) , a))
            ≡⟨⟩ -- Naturality and definitional equality
                ▹ᵏ-C.m k (□ A) (□ B ⊗ C) n
                    ((id {delay □ A by k} * ▹ᵏ-C.m k (□ B) C) n (assoc-right {delay □ A by k} {delay □ B by k} {delay C by k} n
                        (((□-▹ᵏ.at k (□ A) * □-▹ᵏ.at k (□ B)) n
                            ((δ.at A * δ.at B) n (m⁻¹ A B n □A⊗B)))
                        , a)))
            ≡⟨ ▹ᵏ-C.associative k  ⟩
                ▹ᵏ-F.fmap k assoc-right n
                    (▹ᵏ-C.m k (□ A ⊗ □ B) C n
                        ( ⌞ ▹ᵏ-C.m k (□ A) (□ B) n
                            ((□-▹ᵏ.at k (□ A) * □-▹ᵏ.at k (□ B)) n
                                ((δ.at A * δ.at B) n (m⁻¹ A B n □A⊗B))) ⌟
                        , a))
            ≡⟨ cong! (lemma k) ⟩
                ▹ᵏ-F.fmap k assoc-right n
                    (▹ᵏ-C.m k (□ A ⊗ □ B) C n
                        ( □-▹ᵏ.at k (□ A ⊗ □ B) n
                            (□-C.m (□ A) (□ B) n ((δ.at A * δ.at B) n (m⁻¹ A B n □A⊗B)))
                        , a))
            ≡⟨⟩
                ▹ᵏ-F.fmap k assoc-right n
                    (▹ᵏ-C.m k (□ A ⊗ □ B) C n
                        ( ⌞ □-▹ᵏ.at k (□ A ⊗ □ B) n
                            (□-f (m⁻¹ A B) n (δ.at (A ⊗ B) k □A⊗B)) ⌟
                        , a))
            ≡⟨ cong! (□-▹ᵏ.nat-cond k {f = m⁻¹ A B} {n} {δ.at (A ⊗ B) k □A⊗B}) ⟩
                ▹ᵏ-F.fmap k assoc-right n
                    ⌞ (▹ᵏ-C.m k (□ A ⊗ □ B) C n
                        (▹ᵏ-F.fmap k (m⁻¹ A B) n
                            (□-▹ᵏ.at k (□ (A ⊗ B)) n (δ.at (A ⊗ B) k □A⊗B))
                        , a)) ⌟
            ≡⟨ cong! (▹ᵏ-C.m-nat₁ k (m⁻¹ A B) {n}
                        {(□-▹ᵏ.at k (□ (A ⊗ B)) n (δ.at (A ⊗ B) k □A⊗B)) , a}) ⟩
                ▹ᵏ-F.fmap k assoc-right n
                    (▹ᵏ-F.fmap k (m⁻¹ A B * id) n (▹ᵏ-C.m k (□ (A ⊗ B)) C n
                        (□-▹ᵏ.at k (□ (A ⊗ B)) n (δ.at (A ⊗ B) k □A⊗B) , a)))
            ≡⟨ sym (▹ᵏ-F.fmap-∘ k) ⟩
                ▹ᵏ-F.fmap k (assoc-right ∘ m⁻¹ A B * id) n
                    (▹ᵏ-C.m k (□ (A ⊗ B)) C n (□-▹ᵏ.at k (□ (A ⊗ B)) n (δ.at (A ⊗ B) k □A⊗B) , a))
            ≡⟨⟩

                ▹ᵏ-F.fmap (suc k) (assoc-right ∘ m⁻¹ A B * id) (suc n)
                    (▹ᵏ-C.m (suc k) (□ (A ⊗ B)) C (suc n) (□-▹ᵏ.at (suc k) (□ (A ⊗ B)) (suc n) (δ.at (A ⊗ B) (suc k) □A⊗B) , a))
            ∎
        ) ⟩
            ◇-f (assoc-right ∘ m⁻¹ A B * id) (suc n) (st-◇ (A ⊗ B) C (suc n) (□A⊗B , ((suc k) , a)))
        ∎
        where
        lemma : ∀ k -> ▹ᵏ-C.m k (□ A) (□ B) ∘ □-▹ᵏ.at k (□ A) * □-▹ᵏ.at k (□ B)
                     ≈ □-▹ᵏ.at k (□ A ⊗ □ B) ∘ □-C.m (□ A) (□ B)
        lemma zero = refl
        lemma (suc k) {zero} {□□A , □□B} = refl
        lemma (suc k) {suc n} {□□A , □□B} = lemma k




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
    open CartesianFunctor F-cart-▹ renaming (m to m-▹)
    v₂′ : delay B by (k₁ + suc l) at n
    v₂′ rewrite +-suc k₁ l = v₂
    pair-delay-◇ : ∀{A B : τ} -> (k l : ℕ) -> (delay A by k ⊗ delay B by (k + l))
                                   ⇴ delay (A ⊗ ◇ B) by k
    pair-delay-◇ zero l n (dA , dB) = dA , (l , dB)
    pair-delay-◇ {A}{B} (suc k) l n p = Functor.fmap F-▹ (pair-delay-◇ k l) n
        (m-▹ (delay A by k) (delay B by (k + l)) n p)
◇-select {A} {B} n ((.(suc (k₂ + l)) , v₁) , k₂ , v₂)  | greater .k₂ l =
    k₂ , sum-delay k₂ n (inj₁ (sum-delay k₂ n
                        (inj₂ (pair-delay-◇ k₂ (suc l) n (v₁′ , v₂)))))
    where
    open CartesianFunctor F-cart-▹ renaming (m to m-▹)
    v₁′ : delay A by (k₂ + suc l) at n
    v₁′ rewrite +-suc k₂ l = v₁
    pair-delay-◇ : ∀{A B : τ} -> (k l : ℕ) -> (delay A by (k + l) ⊗ delay B by k)
                                   ⇴ delay (◇ A ⊗ B) by k
    pair-delay-◇ zero l n (dA , dB) = (l , dA) , dB
    pair-delay-◇ {A}{B} (suc k) l n p = Functor.fmap F-▹ (pair-delay-◇ k l) n (m-▹ (delay A by (k + l)) (delay B by k) n p)

◇-select {A}{B} n ((k₁ , v₁)              , .k₁ , v₂) | equal .k₁ =
    k₁ , sum-delay k₁ n (inj₂ (m-delay A B n (v₁ , v₂)))
    where open CartesianFunctor (F-cart-delay k₁) renaming (m to m-delay)
