
-- Module for BCCs, CCCs and BCCCs
module CategoryTheory.BCCCs where

open import CategoryTheory.Categories
open import CategoryTheory.BCCCs.Cartesian
open import CategoryTheory.BCCCs.Cocartesian
open import CategoryTheory.BCCCs.Closed

-- Bicartesian categories
record Bicartesian {n} (ℂ : Category n) : Set (lsuc n) where
    field
        cart   : Cartesian ℂ
        cocart : Cocartesian ℂ

-- Cartesian closed categories
record CartesianClosed {n} (ℂ : Category n) : Set (lsuc n) where
    field
        cart   : Cartesian ℂ
        closed : Closed cart

-- Bicartesian closed categories
record BicartesianClosed {n} (ℂ : Category n) : Set (lsuc n) where
    field
        cart   : Cartesian ℂ
        cocart : Cocartesian ℂ
        closed : Closed cart
