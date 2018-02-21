
{- Terms of the language.
   Based on Pfenning and Davies' "Judgmental reconstruction of modal logic."
-}
module Syntax.Terms where

open import Syntax.Types
open import Syntax.Context

mutual
    -- Pure terms of the language, expressed as typing judgements
    infix 10 _⊢_
    data _⊢_ : Environment -> Type -> Set where
        -- | Simply typed lambda calculus
        -- Variables
        var : ∀{Γ Δ A}          ->                  A ∈ Γ
                                                 -----------
                                ->                Δ ⁏ Γ ⊢ A

        -- Lambda abstraction
        lam : ∀{Γ Δ A B}        ->              Δ ⁏ Γ , A ⊢ B
                                               ----------------
                                ->              Δ ⁏ Γ ⊢ A => B

        -- Application
        _$_ : ∀{Γ Δ A B}        ->       Δ ⁏ Γ ⊢ A => B   ->   Δ ⁏ Γ ⊢ A
                                        -------------------------------
                                ->                Δ ⁏ Γ ⊢ B

        -- | Basic data types
        -- Unit                                 ---------------
        unit : ∀{Γ Δ}           ->               Δ ⁏ Γ ⊢ Unit

        -- Pair of two terms
        [_,_] : ∀{Γ Δ A B}      ->        Δ ⁏ Γ ⊢ A   ->   Δ ⁏ Γ ⊢ B
                                         ----------------------------
                                ->               Δ ⁏ Γ ⊢ A & B

        -- First projection
        fst : ∀{Γ Δ A B}        ->               Δ ⁏ Γ ⊢ A & B
                                                ---------------
                                ->                 Δ ⁏ Γ ⊢ A

        -- Second projection
        snd : ∀{Γ Δ A B}        ->               Δ ⁏ Γ ⊢ A & B
                                                ---------------
                                ->                 Δ ⁏ Γ ⊢ B

        -- Left injection
        inl : ∀{Γ Δ A B}        ->                 Δ ⁏ Γ ⊢ A
                                                ---------------
                                ->               Δ ⁏ Γ ⊢ A + B

        -- Right injection
        inr : ∀{Γ Δ A B}        ->                 Δ ⁏ Γ ⊢ B
                                                ---------------
                                ->               Δ ⁏ Γ ⊢ A + B

        -- Case split
        case_inl↦_||inr↦_ : ∀{Γ Δ A B C}
                                ->               Δ ⁏ Γ ⊢ A + B
                                ->      Δ ⁏ Γ , A ⊢ C   ->   Δ ⁏ Γ , B ⊢ C
                                       ------------------------------------
                                ->                 Δ ⁏ Γ ⊢ C

        -- | Modal operators
        -- Stable variables
        svar : ∀{Γ Δ A}         ->                   A ∈ Δ
                                                  -----------
                                ->                 Δ ⁏ Γ ⊢ A

        -- Signal constructor
        sig : ∀{Γ Δ A}          ->                 Δ ⁏ ∙ ⊢ A
                                               ------------------
                                ->              Δ ⁏ Γ ⊢ Signal A

        -- Signal destructor
        letSig_In_ : ∀{Γ Δ A B} ->   Δ ⁏ Γ ⊢ Signal A   ->   Δ , A ⁏ Γ ⊢ B
                                    ----------------------------------------
                                ->                 Δ ⁏ Γ ⊢ B

        -- Event constructor
        event : ∀{Γ Δ A}        ->                 Δ ⁏ Γ ⊨ A
                                               ------------------
                                ->              Δ ⁏ Γ ⊢ Event A

    -- Computational terms of the language
    infix 10 _⊨_
    data _⊨_ : Environment -> Type -> Set where
        -- Pure term is a computational term
        pure : ∀{Γ Δ A}          ->                 Δ ⁏ Γ ⊢ A
                                                  -------------
                                 ->                 Δ ⁏ Γ ⊨ A

        -- Computational signal destructor
        letSig_InC_ : ∀{Γ Δ A B} ->   Δ ⁏ Γ ⊢ Signal A   ->   Δ , A ⁏ Γ ⊨ B
                                     ----------------------------------------
                                 ->                 Δ ⁏ Γ ⊨ B

        -- Event destructor
        letEvt_In_ : ∀{Γ Δ A B}  ->   Δ ⁏ Γ ⊢ Event A   ->   Δ ⁏ [ A ] ⊨ B
                                     ----------------------------------------
                                 ->                 Δ ⁏ Γ ⊨ B

        -- Select the event that happens first
        select_↦_||_↦_||both↦_ : ∀{Γ Δ A B C}
            ->   Δ ⁏ Γ ⊢ Event A   ->   Δ ⁏ [ A ] , Event B ⊨ C   -- A happens first
            ->   Δ ⁏ Γ ⊢ Event B   ->   Δ ⁏ [ B ] , Event A ⊨ C   -- B happens first
            ->              Δ ⁏ ∙ , A , B ⊨ C                     -- A and B happen at the same time
                -------------------------------------------------
            ->                  Δ ⁏ Γ ⊨ C
