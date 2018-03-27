
{- Terms of the language.
   Based on Pfenning and Davies' "Judgmental reconstruction of modal logic."
-}
module Syntax.Terms where

open import Syntax.Types
open import Syntax.Context

mutual
    -- Pure terms of the language, expressed as typing judgements
    infix 10 _⊢_
    data _⊢_ : Context -> Judgement -> Set where
        -- | Simply typed lambda calculus
        -- Variables
        var : ∀{Γ A}            ->                 A now ∈ Γ
                                                  -----------
                                ->                 Γ ⊢ A now

        -- Lambda abstraction
        lam : ∀{Γ A B}          ->             Γ , A now ⊢ B now
                                              -------------------
                                ->               Γ ⊢ A => B now

        -- Application
        _$_ : ∀{Γ A B}          ->         Γ ⊢ A => B now  ->   Γ ⊢ A now
                                          -------------------------------
                                ->                  Γ ⊢ B now

        -- | Basic data types
        -- Unit                                  ---------------
        unit : ∀{Γ}             ->                Γ ⊢ Unit now

        -- Pair of two terms
        [_,,_] : ∀{Γ A B}       ->          Γ ⊢ A now   ->   Γ ⊢ B now
                                        ----------------------------
                                ->                 Γ ⊢ A & B now

        -- First projection
        fst : ∀{Γ A B}          ->                 Γ ⊢ A & B now
                                                  ---------------
                                ->                   Γ ⊢ A now

        -- Second projection
        snd : ∀{Γ A B}          ->                 Γ ⊢ A & B now
                                                  ---------------
                                ->                   Γ ⊢ B now

        -- Left injection
        inl : ∀{Γ A B}          ->                   Γ ⊢ A now
                                                  ---------------
                                ->                 Γ ⊢ A + B now

        -- Right injection
        inr : ∀{Γ A B}          ->                   Γ ⊢ B now
                                                  ---------------
                                ->                 Γ ⊢ A + B now

        -- Case split
        case_inl↦_||inr↦_ : ∀{Γ A B C}
                                ->                 Γ ⊢ A + B now
                                ->    Γ , A now ⊢ C now  ->   Γ , B now ⊢ C now
                                     -------------------------------------------
                                ->                   Γ ⊢ C now

        -- | Modal operators
        -- Stable variables
        svar : ∀{Γ A}           ->                 A always ∈ Γ
                                                  --------------
                                ->                 Γ ⊢ A always

        -- A stable type is available now
        present : ∀{Γ A}        ->                 Γ ⊢ A always
                                                  --------------
                                ->                   Γ ⊢ A now

        -- Types in stable contexts are always inhabited
        stable : ∀{Γ A}         ->                 Γ ˢ ⊢ A now
                                                  --------------
                                ->                 Γ ⊢ A always

        -- Signal constructor
        sig : ∀{Γ A}            ->                Γ ⊢ A always
                                               ------------------
                                ->              Γ ⊢ Signal A now

        -- Signal destructor
        letSig_In_ : ∀{Γ A B}   ->   Γ ⊢ Signal A now  ->   Γ , A always ⊢ B now
                                    ----------------------------------------
                                ->                 Γ ⊢ B now

        -- Event constructor
        event : ∀{Γ A}          ->                 Γ ⊨ A now
                                               ------------------
                                ->              Γ ⊢ Event A now

    -- Computational terms of the language
    infix 10 _⊨_
    data _⊨_ : Context -> Judgement -> Set where
        -- Pure term is a computational term
        pure : ∀{Γ A}           ->                   Γ ⊢ A
                                                    -------
                                ->                   Γ ⊨ A

        -- Computational signal destructor
        letSig_InC_ : ∀{Γ A B}  ->   Γ ⊢ Signal A now   ->   Γ , A now ⊨ B now
                                    -------------------------------------------
                                ->                 Γ ⊨ B now

        -- Event destructor
        letEvt_In_ : ∀{Γ A B}   ->   Γ ⊢ Event A now  ->   Γ ˢ , A now  ⊨ B now
                                    ----------------------------------------
                                ->                 Γ ⊨ B now

        -- Select the event that happens first
        select_↦_||_↦_||both↦_ : ∀{Γ A B C}
            ->   Γ ⊢ Event A now  ->  Γ ˢ , Event B now , A now ⊨ C now   -- A happens first
            ->   Γ ⊢ Event B now  ->  Γ ˢ , Event A now , B now ⊨ C now   -- B happens first
            ->             Γ ˢ , A now , B now ⊨ C now                    -- A and B happen at the same time
                -------------------------------------------------
            ->                  Γ ⊨ C now
