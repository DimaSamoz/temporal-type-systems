{-# OPTIONS --allow-unsolved-metas #-}
{- Diamond operator. -}
module TemporalOps.Diamond where

open import CategoryTheory.Categories
open import CategoryTheory.Instances.Reactive
open import CategoryTheory.Functor
open import CategoryTheory.NatTrans
open import CategoryTheory.Monad
open import TemporalOps.Common
open import TemporalOps.Next
open import TemporalOps.Delay
open import TemporalOps.Diamond.Functor public
open import TemporalOps.Diamond.Join
open import TemporalOps.Diamond.JoinLemmas

import Relation.Binary.PropositionalEquality as ≡
open import Data.Product
open import Relation.Binary.HeterogeneousEquality as ≅
            using (_≅_ ; ≅-to-≡ ; ≡-to-≅ ; cong₂)
open import Data.Nat.Properties
            using (+-identityʳ ; +-comm ; +-suc ; +-assoc)


M-◇ : Monad ℝeactive
M-◇ = record
    { T = F-◇
    ; η = η-◇
    ; μ = μ-◇
    ; η-unit1 = refl
    ; η-unit2 = η-unit2-◇
    ; μ-assoc = λ{A}{n}{k} -> μ-assoc-◇ {A} {n} {k}
    }
    where
    η-◇ : I ⟹ F-◇
    η-◇ = record
        { at = λ A n x -> zero , x
        ; nat-cond = λ {A} {B} {f} {n} {a} → refl }

    private module μ = _⟹_ μ-◇
    private module η = _⟹_ η-◇
    private module F-◇ = Functor F-◇
    open ≡.≡-Reasoning

    η-unit2-◇ : {A : τ} {n : ℕ} {a : ◇ A at n} → (μ.at A n (F-◇.fmap (η.at A) n a)) ≡ a
    η-unit2-◇ {A} {n} {k , v} with inspect (compareLeq k n)
    -- n = k + l
    η-unit2-◇ {A} {.(k + l)} {k , v} | snd==[ .k + l ] with≡ pf =
        begin
            μ.at A (k + l) (F-◇.fmap (η.at A) (k + l) (k , v))
        ≡⟨⟩
            μ.at A (k + l) (k , (Functor.fmap (F-delay k) (η.at A) at (k + l)) v)
        ≡⟨⟩
            μ-compare A (k + l) k ((Functor.fmap (F-delay k) (η.at A) at (k + l)) v) (compareLeq k (k + l))
        ≡⟨ cong (λ x → μ-compare A (k + l) k ((Functor.fmap (F-delay k) (η.at A) at (k + l)) v) x) pf ⟩
            μ-compare A (k + l) k ((Functor.fmap (F-delay k) (η.at A) at (k + l)) v) snd==[ k + l ]
        ≡⟨⟩
            μ-shift k l (rew (delay-+-left0 k l) ((Functor.fmap (F-delay k) (η.at A) at (k + l)) v))
        ≡⟨ cong (λ x → μ-shift k l x)
            (delay-+-left0-eq k l ((Functor.fmap (F-delay k) (η.at A) at (k + l)) v)
                                          ((Functor.fmap (F-delay (k + 0)) (η.at A) at (k + l)) v′) pr)
         ⟩
            μ-shift k l (rew (delay-+ k 0 l) ((Functor.fmap (F-delay (k + 0)) (η.at A) at (k + l)) v′))
        ≡⟨ cong (λ x → μ-shift k l x) (fmap-delay-+-n+k k 0 l v′) ⟩
            μ-shift k l ((Functor.fmap (F-delay 0) (η.at A) at l) (rew (delay-+ k 0 l) v′))
        ≡⟨⟩ -- Def. of Functor.fmap (F-delay 0)
            μ-shift k l ((η.at A) l (rew (delay-+ k 0 l) v′))
        ≡⟨⟩ -- Def. of η.at
            μ-shift k l (0 , rew (delay-+ k 0 l) v′)
        ≡⟨⟩
            k + 0 , rew (sym (delay-+ k 0 l)) (rew (delay-+ k 0 l) v′)
        ≡⟨ cong (λ x → k + 0 , x) (rew-cancel v′ (delay-+ k 0 l)) ⟩
            k + 0 , rew (delay-+0-left k (k + l)) v
        ≡⟨ ≅-to-≡ {_} {◇ A at (k + l)}
            (cong₂ {A = ℕ} {_} {λ n v → ◇ A at (k + l)}
                (λ x y → x , y) (≡-to-≅ (+-identityʳ k)) (≅.sym v≅v′)) ⟩
            k , v
        ∎
        where
        v′ : delay A by (k + 0) at (k + l)
        v′ = rew (delay-+0-left k (k + l)) v
        v≅v′ : v ≅ v′
        v≅v′ = rew-to-≅ (delay-+0-left k (k + l))
        pr : (Functor.fmap (F-delay k) (η.at A) at (k + l)) v
           ≅ (Functor.fmap (F-delay (k + 0)) (η.at A) at (k + l)) v′
        pr = cong₂ (λ x y → (Functor.fmap (F-delay x) (η.at A) at (k + l)) y)
                        (≡-to-≅ (sym (+-identityʳ k))) v≅v′
        v-no-delay : A at l
        v-no-delay = rew (delay-+-left0 k l) v

    -- k = suc n + l
    η-unit2-◇ {A} {n} {.(n + suc l) , v} | fst==suc[ .n + l ] with≡ pf =
        begin
            μ.at A n (F-◇.fmap (η.at A) n (n + suc l , v))
        ≡⟨⟩
            μ.at A n (n + suc l , (Functor.fmap (F-delay (n + suc l)) (η.at A) at n) v)
        ≡⟨⟩
            μ-compare A n (n + suc l) ((Functor.fmap (F-delay (n + suc l)) (η.at A) at n) v) (compareLeq (n + suc l) n)
        ≡⟨ cong (λ x → μ-compare A n (n + suc l) ((Functor.fmap (F-delay (n + suc l)) (η.at A) at n) v) x) pf ⟩
            μ-compare A n (n + suc l) ((Functor.fmap (F-delay (n + suc l)) (η.at A) at n) v) fst==suc[ n + l ]
        ≡⟨⟩
            n + suc l , rew (delay-⊤ n l) top.tt
        ≡⟨ cong (λ x → n + suc l , x) (eq n l v) ⟩
            n + suc l , v
        ∎
        where
        eq : ∀ (n l : ℕ) -> (v : delay A by (n + suc l) at n )
          -> rew (delay-⊤ n l) top.tt
           ≡ v
        eq zero l v = refl
        eq (suc n) l v = eq n l v

    μ-assoc-◇ : {A : τ} {n : ℕ} {a : ◇ ◇ ◇ A at n}
             -> (μ.at A n (μ.at (F-◇.omap A) n a))
              ≡ (μ.at A n (F-◇.fmap (μ.at A) n a))
    μ-assoc-◇ {A} {n} {k , v} with inspect (compareLeq k n)
    -- n = k + l
    μ-assoc-◇ {A} {.(k + l)} {k , v} | snd==[ .k + l ] with≡ pf =
        begin
            μ.at A (k + l) (μ.at (F-◇.omap A) (k + l) (k , v))
        ≡⟨⟩
            μ.at A (k + l) (μ-compare (F-◇.omap A) (k + l) k v (compareLeq k (k + l)))
        ≡⟨ cong (λ x → μ.at A (k + l) (μ-compare (F-◇.omap A) (k + l) k v (x))) pf ⟩
            μ.at A (k + l) (μ-compare (F-◇.omap A) (k + l) k v (snd==[ k + l ]))
        ≡⟨⟩
            μ.at A (k + l) (μ-shift k l (rew (delay-+-left0 k l) v))
        ≡⟨ ≅-to-≡ (μ-interchange {A} {l} {k} {rew (delay-+-left0 k l) v}) ⟩
            μ-shift k l (μ.at A l (rew (delay-+-left0 k l) v))
        ≡⟨ cong (λ x → μ-shift k l (μ.at A l x)) (v≡v′-rew k l v v′ v≅v′) ⟩
            μ-shift k l (μ.at A l (rew (delay-+ k 0 l) v′))
        ≡⟨⟩ -- Def. of (F-delay 0).fmap
            μ-shift k l ((Functor.fmap (F-delay 0) (μ.at A) at l) (rew (delay-+ k 0 l) v′))
        ≡⟨ cong (λ x → μ-shift k l x) (sym (fmap-delay-+-n+k k 0 l v′)) ⟩
            μ-shift k l (rew (delay-+ k 0 l) ((Functor.fmap (F-delay (k + 0)) (μ.at A) at (k + l)) v′))
        ≡⟨ cong (λ x → μ-shift k l x)
            (sym (delay-+-left0-eq k l ((Functor.fmap (F-delay k) (μ.at A) at (k + l)) v)
                                       ((Functor.fmap (F-delay (k + 0)) (μ.at A) at (k + l)) v′) pr))
         ⟩
            μ-shift k l (rew (delay-+-left0 k l) ((Functor.fmap (F-delay k) (μ.at A) at (k + l)) v))
        ≡⟨⟩
            μ-compare A (k + l) k ((Functor.fmap (F-delay k) (μ.at A) at (k + l)) v) (snd==[ k + l ])
        ≡⟨ cong (λ x → μ-compare A (k + l) k ((Functor.fmap (F-delay k) (μ.at A) at (k + l)) v) x) (sym pf) ⟩
            μ-compare A (k + l) k ((Functor.fmap (F-delay k) (μ.at A) at (k + l)) v) (compareLeq k (k + l))
        ≡⟨⟩
            μ.at A (k + l) (k , (Functor.fmap (F-delay k) (μ.at A) at (k + l)) v)
        ≡⟨⟩
            μ.at A (k + l) (F-◇.fmap (μ.at A) (k + l) (k , v))
        ∎
        where
        v′ : delay (◇ ◇ A) by (k + 0) at (k + l)
        v′ = rew (delay-+0-left k (k + l)) v
        v≅v′ : v ≅ v′
        v≅v′ = rew-to-≅ (delay-+0-left k (k + l))
        pr : (Functor.fmap (F-delay k) (μ.at A) at (k + l)) v
           ≅ (Functor.fmap (F-delay (k + 0)) (μ.at A) at (k + l)) v′
        pr = ≅.cong₂ (λ x y → (Functor.fmap (F-delay x) (μ.at A) at (k + l)) y)
                (≡-to-≅ (sym (+-identityʳ k))) v≅v′
        v≡v′-rew : ∀ {A} (k l : ℕ) -> Proof-≡ (delay-+-left0 {A} k l)
                                              (delay-+ {A} k 0 l)
        v≡v′-rew zero l v v′ ≅.refl = refl
        v≡v′-rew (suc k) l = v≡v′-rew k l
    -- k = suc n + l
    μ-assoc-◇ {A} {.n} {.(n + suc l) , v} | fst==suc[ n + l ] with≡ pf =
        begin
            μ.at A n (μ.at (F-◇.omap A) n (n + suc l , v))
        ≡⟨⟩
            μ.at A n (μ-compare (F-◇.omap A) n (n + suc l) v (compareLeq (n + suc l) n))
        ≡⟨ cong (λ x → μ.at A n (μ-compare (F-◇.omap A) n (n + suc l) v x)) pf ⟩
            μ.at A n (μ-compare (F-◇.omap A) n (n + suc l) v (fst==suc[ n + l ]))
        ≡⟨⟩
            μ.at A n (n + suc l , rew (delay-⊤ n l) top.tt)
        ≡⟨⟩
            μ-compare A n (n + suc l) (rew (delay-⊤ n l) top.tt) (compareLeq (n + suc l) n)
        ≡⟨ cong (λ x → μ-compare A n (n + suc l) (rew (delay-⊤ n l) top.tt) x) pf ⟩
            μ-compare A n (n + suc l) (rew (delay-⊤ n l) top.tt) (fst==suc[ n + l ])
        ≡⟨⟩
            n + suc l , rew (delay-⊤ n l) top.tt
        ≡⟨⟩
            μ-compare A n (n + suc l) ((Functor.fmap (F-delay (n + suc l)) (μ.at A) at n) v) (fst==suc[ n + l ])
        ≡⟨ cong (λ x -> μ-compare A n (n + suc l) ((Functor.fmap (F-delay (n + suc l)) (μ.at A) at n) v) x) (sym pf) ⟩
            μ-compare A n (n + suc l) ((Functor.fmap (F-delay (n + suc l)) (μ.at A) at n) v) (compareLeq (n + suc l) n)
        ≡⟨⟩
            μ.at A n (n + suc l , (Functor.fmap (F-delay (n + suc l)) (μ.at A) at n) v)
        ≡⟨⟩
            μ.at A n (F-◇.fmap (μ.at A) n (n + suc l , v))
        ∎

-- | Monadic operations

open Monad M-◇
private module μ = _⟹_ μ
private module η = _⟹_ η
open Functor F-◇
open import Data.Nat
open import Data.Sum
open ≡.≡-Reasoning

-- Bind operator
_>>=_ : ∀{A B : τ}{n : ℕ} -> (◇ A) n -> (A ⇴ (◇ B)) -> (◇ B) n
_>>=_ {A}{B} {n} a f = μ.at B n (fmap f n a)

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
    lemma : (((μ.at C ∘ μ.at (◇ C)) ∘ fmap (fmap g)) ∘ fmap f) n a
          ≡ (((μ.at C ∘ fmap (μ.at C)) ∘ fmap (fmap g)) ∘ fmap f) n a
    lemma rewrite μ-assoc {C} {n} {((fmap (fmap g)) ∘ fmap f) n a} = refl

-- Return is right unit to bind
>>=-unit-right : ∀{A : τ}{n : ℕ} -> (a : (◇ A) n)
         -> a >>= η.at A ≡ a
>>=-unit-right a = η-unit2


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
