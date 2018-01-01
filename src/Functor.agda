
{- Functoriality of temporal operators -}
module Functor where

open import Categories
open import TemporalOps
open import Relation.Binary.PropositionalEquality


-- || Functoriality of ▹

-- Lifting of ▹
fmap-▹ : {A B : τ} -> A ⇴ B -> ▹ A ⇴ ▹ B
fmap-▹ f zero =  λ _ → top.tt
fmap-▹ f (suc n) = f n

-- ▹ preserves identities
fmap-▹-id : ∀{A : τ} {n : ℕ}
         -> fmap-▹ id at n ≡ id {▹ A} at n
fmap-▹-id {n = zero} = refl
fmap-▹-id {n = suc n} = refl

-- ▹ preserves composition
fmap-▹-∘ : ∀ {A B C : τ} {n : ℕ} {g : B ⇴ C} {f : A ⇴ B}
        -> fmap-▹ (g ∘ f) at n ≡ fmap-▹ g ∘ fmap-▹ f at n
fmap-▹-∘ {n = zero} = refl
fmap-▹-∘ {n = suc n} = refl


-- || Functoriality of delay

-- Delay of the iterated delay operator
fmap-delay : {A B : τ} -> (n : ℕ) -> A ⇴ B -> delay A by n ⇴ delay B by n
fmap-delay zero    f = f
fmap-delay (suc k) f = fmap-▹ (fmap-delay k f)

-- Delay preserves identities
fmap-delay-id : ∀{A : τ} {n k : ℕ}
             -> fmap-delay k id at n ≡ id {delay A by k} at n
fmap-delay-id {k = zero} = refl
fmap-delay-id {A} {zero} {suc l} = refl
fmap-delay-id {A} {suc n} {suc l} = fmap-delay-id {A} {n} {l}

-- Delay preserves composition
fmap-delay-∘ : ∀{A B C : τ} {n k : ℕ} {g : B ⇴ C} {f : A ⇴ B}
            -> fmap-delay k (g ∘ f) at n ≡ fmap-delay k g ∘ fmap-delay k f at n
fmap-delay-∘ {k = zero} = refl
fmap-delay-∘ {n = zero} {suc l} = refl
fmap-delay-∘ {n = suc m} {suc l} = fmap-delay-∘ {n = m} {k = l}


-- || Functoriality of ◇

-- Lifting of ◇
fmap-◇ : {A B : τ} -> A ⇴ B -> ◇ A ⇴ ◇ B
fmap-◇ f n (k , v) = k , (fmap-delay k f at n) v

-- ◇ preserves identities
fmap-◇-id : ∀{A : τ} {n : ℕ} {a : (◇ A) n}
         -> (fmap-◇ id at n) a ≡ (id {◇ A} at n) a
fmap-◇-id {A} {n} {zero , v} = refl
fmap-◇-id {A} {zero} {suc k , v} = refl
fmap-◇-id {A} {suc n} {suc k , v}
    rewrite delay-plus {A} 1 k n
          | fmap-delay-id {A} {n} {k} = refl

-- ◇ preserves composition
fmap-◇-∘ : ∀ {A B C : τ} {n : ℕ} {a : (◇ A) n} {g : B ⇴ C} {f : A ⇴ B}
        -> (fmap-◇ (g ∘ f) at n) a ≡ (fmap-◇ g ∘ fmap-◇ f at n) a
fmap-◇-∘ {n = n} {zero , v} = refl
fmap-◇-∘ {n = zero} {suc k , v} = refl
fmap-◇-∘ {A} {B} {C} {n = suc n} {suc k , v} {g} {f}
    rewrite delay-plus {A} 1 k n
          | fmap-delay-∘ {A} {B} {C} {n} {k} {g} {f} = refl

-- || Functoriality of □

-- Lifting of □
fmap-□ : {A B : τ} -> A ⇴ B -> □ A ⇴ □ B
fmap-□ f n a = λ k → f k (a k)

-- □ preserves identities
fmap-□-id : ∀{A : τ}
         -> fmap-□ id ≡ id {□ A}
fmap-□-id = refl

-- □ preserves composition
fmap-□-∘ : ∀ {A B C : τ} {g : B ⇴ C} {f : A ⇴ B}
        -> fmap-□ (g ∘ f) ≡ fmap-□ g ∘ fmap-□ f
fmap-□-∘ = refl
