
module TemporalOps.StrongMonad where

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
open import TemporalOps.Diamond.Join
open import TemporalOps.Box
open import TemporalOps.Common.Other
open import TemporalOps.Common.Compare
open import TemporalOps.Common.Rewriting
open import TemporalOps.OtherOps

open import Relation.Binary.PropositionalEquality as ≡ hiding (inspect)
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

◇-□-Strong : WStrongMonad ℝeactive-cart M-◇ W-cart-□
◇-□-Strong = record
    { st = st-◇
    ; st-nat₁ = st-nat₁-◇
    ; st-nat₂ = st-nat₂-◇
    ; st-λ = st-λ-◇
    ; st-α = st-α-◇
    ; st-η = refl
    ; st-μ = λ{A}{B}{n}{a} -> st-μ-◇ {A}{B}{n}{a}
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
    st-α-◇ {A} {B} {C} {n} {□A⊗B , (k , a)} =
        begin
            st-◇ A (□ B ⊗ C) n
                (□-f π₁ n □A⊗B , st-◇ B C n (□-f π₂ n □A⊗B , (k , a)))
        ≡⟨ cong (λ x → k , x) (
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

                ▹ᵏ-F.fmap k (assoc-right ∘ m⁻¹ A B * id) n
                    (▹ᵏ-C.m k (□ (A ⊗ B)) C n (□-▹ᵏ.at k (□ (A ⊗ B)) n (δ.at (A ⊗ B) k □A⊗B) , a))
            ∎
        ) ⟩
            ◇-f (assoc-right ∘ m⁻¹ A B * id) n (st-◇ (A ⊗ B) C n (□A⊗B , (k , a)))
        ∎
        where
        lemma : ∀ k -> ▹ᵏ-C.m k (□ A) (□ B) ∘ □-▹ᵏ.at k (□ A) * □-▹ᵏ.at k (□ B)
                     ≈ □-▹ᵏ.at k (□ A ⊗ □ B) ∘ □-C.m (□ A) (□ B)
        lemma zero = refl
        lemma (suc k) {zero} {□□A , □□B} = refl
        lemma (suc k) {suc n} {□□A , □□B} = lemma k

    st-μ-◇ : ∀{A B : τ}
          -> μ.at (□ A ⊗ B) ∘ ◇-f (st-◇ A B) ∘ st-◇ A (◇ B)
           ≈ st-◇ A B ∘ (id * μ.at B)
    st-μ-◇ {A} {B} {n} {□A , (k , a)} with inspect (compareLeq k n)
    st-μ-◇ {A} {B} {.(k + l)} {□A , k , a} | snd==[ .k + l ] with≡ pf =
        begin
            μ.at (□ A ⊗ B) (k + l) (◇-f (st-◇ A B) (k + l) (st-◇ A (◇ B) (k + l) (□A , (k , a))))
        ≡⟨⟩
            μ-compare (□ A ⊗ B) (k + l) k
                (▹ᵏ-F.fmap k (st-◇ A B) (k + l)
                    (▹ᵏ-C.m k (□ A) (◇ B) (k + l)
                        (□-▹ᵏ.at k (□ A) (k + l) (δ.at A (k + l) □A) , a)))
                            (⌞ compareLeq k (k + l) ⌟)
        ≡⟨ cong! pf ⟩
            μ-compare (□ A ⊗ B) (k + l) k
                (▹ᵏ-F.fmap k (st-◇ A B) (k + l)
                    (▹ᵏ-C.m k (□ A) (◇ B) (k + l)
                        (□-▹ᵏ.at k (□ A) (k + l) (δ.at A (k + l) □A) , a)))
                            (snd==[ k + l ])
        ≡⟨⟩
            μ-shift k l
                (rew (delay-+-left0 k l)
                    (▹ᵏ-F.fmap k (st-◇ A B) (k + l)
                        (▹ᵏ-C.m k (□ A) (◇ B) (k + l)
                            ( □-▹ᵏ.at k (□ A) (k + l) (δ.at A (k + l) □A)
                            , a))))
        ≡⟨ cong (μ-shift k l) (fmap-delay-+-n+0 k l) ⟩
            μ-shift k l
                (st-◇ A B l
                    (rew (delay-+-left0 k l)
                        (▹ᵏ-C.m k (□ A) (◇ B) (k + l)
                            ( □-▹ᵏ.at k (□ A) (k + l) (δ.at A (k + l) □A)
                            , a))))
        ≡⟨ cong (λ x → μ-shift k l (st-◇ A B l x)) (m-delay-+-n+0 k l) ⟩
            μ-shift k l
                (st-◇ A B l
                    ( rew (delay-+-left0 k l) (□-▹ᵏ.at k (□ A) (k + l) (δ.at A (k + l) □A))
                    , rew (delay-+-left0 k l) a))
        ≡⟨ cong (λ x → μ-shift k l (st-◇ A B l (x , _))) (rew-□-left0 k l) ⟩
            μ-shift k l (st-◇ A B l (□A , rew (delay-+-left0 k l) a))
         ≡⟨ lemma k l (rew (delay-+-left0 k l) a) ⟩
            st-◇ A B (k + l) (□A , μ-shift k l (rew (delay-+-left0 k l) a))
        ≡⟨⟩
            st-◇ A B (k + l) (□A , μ-compare B (k + l) k a (⌞ snd==[ k + l ] ⌟))
        ≡⟨ cong! pf ⟩
            st-◇ A B (k + l) (□A , μ.at B (k + l) (k , a))
        ∎
        where
        rew-□-left0 : ∀ k l
             -> rew (delay-+-left0 k l) (□-▹ᵏ.at k (□ A) (k + l) (δ.at A (k + l) □A))
              ≡ □A
        rew-□-left0 zero l = refl
        rew-□-left0 (suc k) l = rew-□-left0 k l

        rew-□ : ∀ k l m
             -> rew (sym (delay-+ k m l)) (□-▹ᵏ.at m (□ A) l (δ.at A m □A))
              ≡ □-▹ᵏ.at (k + m) (□ A) (k + l) (δ.at A (k + m) □A)
        rew-□ zero l m = refl
        rew-□ (suc k) l m = rew-□ k l m

        lemma : ∀ k l a
             -> μ-shift k l (st-◇ A B l (□A , a))
              ≡ st-◇ A B (k + l) (□A , μ-shift k l a)
        lemma k l (m , a) =
            begin
                μ-shift k l (st-◇ A B l (□A , (m , a)))
            ≡⟨⟩
                k + m , rew (sym (delay-+ k m l)) (▹ᵏ-C.m m (□ A) B l (□-▹ᵏ.at m (□ A) l (δ.at A m □A) , a))
            ≡⟨ cong (λ x -> _ , x) (m-delay-+-sym k l m) ⟩
                k + m , ▹ᵏ-C.m (k + m) (□ A) B (k + l)
                            ( rew (sym (delay-+ k m l)) (□-▹ᵏ.at m (□ A) l (δ.at A m □A))
                            , rew (sym (delay-+ k m l)) a)
            ≡⟨ cong (λ x → _ , ▹ᵏ-C.m (k + m) (□ A) B (k + l) (x , _)) (rew-□ k l m) ⟩
                k + m , ▹ᵏ-C.m (k + m) (□ A) B (k + l)
                            ( □-▹ᵏ.at (k + m) (□ A) (k + l) (δ.at A (k + m) □A)
                            , rew (sym (delay-+ k m l)) a)
            ≡⟨⟩
                st-◇ A B (k + l) (□A , (k + m , rew (sym (delay-+ k m l)) a))
            ∎

    st-μ-◇ {A} {B} {.n} {□A , .(n + suc l) , a} | fst==suc[ n + l ] with≡ pf =
        begin
            μ.at (□ A ⊗ B) n (◇-f (st-◇ A B) n (st-◇ A (◇ B) n (□A , (n + suc l , a))))
        ≡⟨⟩
            μ-compare (□ A ⊗ B) n (n + suc l)
                (▹ᵏ-F.fmap (n + suc l) (st-◇ A B) n
                    (▹ᵏ-C.m (n + suc l) (□ A) (◇ B) n
                    (□-▹ᵏ.at (n + suc l) (□ A) n
                    (δ.at A (n + suc l) □A) , a)))
                    (⌞ compareLeq (n + suc l) n ⌟)
        ≡⟨ cong! pf ⟩
            μ-compare (□ A ⊗ B) n (n + suc l)
                (▹ᵏ-F.fmap (n + suc l) (st-◇ A B) n
                    (▹ᵏ-C.m (n + suc l) (□ A) (◇ B) n
                    (□-▹ᵏ.at (n + suc l) (□ A) n
                    (δ.at A (n + suc l) □A) , a)))
                    (fst==suc[ n + l ])
        ≡⟨⟩
            n + suc l , rew (delay-⊤ n l) top.tt
        ≡⟨ cong (λ x -> _ , x) (lemma n l) ⟩
            n + suc l , ▹ᵏ-C.m (n + suc l) (□ A) B n (□-▹ᵏ.at (n + suc l) (□ A) n (δ.at A (n + suc l) □A) , rew (delay-⊤ n l) top.tt)
        ≡⟨⟩
            st-◇ A B n (□A , μ-compare B n (n + suc l) a (⌞ fst==suc[ n + l ] ⌟))
        ≡⟨ cong! pf ⟩
            st-◇ A B n (□A , μ.at B n ((n + suc l) , a))
        ∎
        where
        lemma : ∀ n l
             -> rew (delay-⊤ n l) top.tt
              ≡ ▹ᵏ-C.m (n + suc l) (□ A) B n (□-▹ᵏ.at (n + suc l) (□ A) n (δ.at A (n + suc l) □A)
                                            , rew (delay-⊤ n l) top.tt)
        lemma zero l = refl
        lemma (suc n) l = lemma n l
