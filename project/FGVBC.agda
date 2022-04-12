module FGVBC where

open import Data.Nat
open import Data.List using (List; []; _∷_)

open import Level renaming (zero to lzero; suc to lsuc; _⊔_ to _⊔ˡ_)
open import Categories.Category
open import Categories.Category.Instance.Sets

import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)


-----------------------------------------------------------------------------------------------------
-- A postulate is a declaration of an element of some type without 
-- an accompanying definition. With postulates we can introduce 
-- elements in a type without actually giving the definition of 
-- the element itself.

postulate     -- Think of it as some universal set of states
  State : Set₀
  Exceptions : Set₀

-- Types of lambda calculus:
data Typ : Set where
    Unit : Typ                -- unit
    Bool : Typ                -- bool   
    _⇒_ : Typ → Typ → Typ    -- function
    Exc : Typ                 -- exception
    TState : Typ              -- State

-- Context
Ctx = List Typ
_,,_ : Ctx → Typ → Ctx
Γ ,, τ = τ ∷ Γ

infixr 10 _⇒_
infixr 8 _⊢ⱽ_

-- de Bruijn indices
data _∈_ {A : Set} : (x : A) (l : List A) → Set where -- type \in
  i0 : {x : A} {xs : List A} → x ∈ (x ∷ xs)
  iS : {x y : A} {xs : List A} → x ∈ xs → x ∈ (y ∷ xs) 

mutual
  -- Judgement for values
  data _⊢ⱽ_ (Γ : Ctx) : Typ → Set where
    χ : {t : Typ} → t ∈ Γ → Γ ⊢ⱽ t     -- variable
    const : State → Γ ⊢ⱽ TState        -- every s ∈ State is a value
    ⋆ : Γ ⊢ⱽ Unit                      -- unit
    true : Γ ⊢ⱽ Bool                   -- true
    false : Γ ⊢ⱽ Bool                  -- false
    exceptions : Exceptions → Γ ⊢ⱽ Exc
    lam : {t₁ t₂ : Typ} → (Γ ,, t₁) ⊢ᶜ t₂ → Γ ⊢ⱽ t₁ ⇒ t₂

  -- Judgment for computations
  data _⊢ᶜ_ (Γ : Ctx) : Typ → Set where
    return : {t : Typ} → Γ ⊢ⱽ t → Γ ⊢ᶜ t
    LET_IN_ : {t₁ t₂ : Typ} →  Γ ⊢ⱽ t₁ → (Γ ,, t₁) ⊢ᶜ t₂ → Γ ⊢ᶜ t₂
    app : {t₁ t₂ : Typ} → Γ ⊢ⱽ t₁ ⇒ t₂ → Γ ⊢ⱽ t₁ → Γ ⊢ᶜ t₂           -- Preveri v / c
    raise : {t : Typ} → Γ ⊢ⱽ Exc → Γ ⊢ᶜ t                             -- Preveri
    -- get : {t : Typ}


  