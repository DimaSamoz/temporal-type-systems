
{- Type system of the language. -}
module Syntax.Types where

-- Abstract syntax of types for the language.
data Type : Set where
    -- Unit type
    Unit   : Type
    -- Product type
    _&_    : Type -> Type -> Type
    -- Sum type
    _+_    : Type -> Type -> Type
    -- Function type
    _=>_   : Type -> Type -> Type
    -- Event type
    Event  : Type -> Type
    -- Signal type
    Signal : Type -> Type
infixr 65 _=>_
infixl 68 _+_
infixl 70 _&_
