module FGVBC where

open import Data.Nat
open import Data.Bool 
open import Data.Product using (_×_)
open import Agda.Builtin.Unit 
open import Data.List using (List; []; _∷_)

open import Level renaming (zero to lzero; suc to lsuc; _⊔_ to _⊔ˡ_)
open import Categories.Category
open import Categories.Category.Instance.Sets

import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)

-- open Monad.Update.Update using (T)

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
    unit : Typ                -- unit
    bool : Typ                -- bool   
    _⇒_ : Typ → Typ → Typ    -- function
    TState : Typ              -- State

-- Context
Ctx = List Typ
_,,_ : Ctx → Typ → Ctx
Γ ,, τ = τ ∷ Γ

infixr 10 _⇒_
infixr 9 _,,_
infixr 8 _⊢ⱽ_
infixr 8 _⊢ᶜ_

-- de Bruijn indices
data _∈_ {A : Set} : (x : A) (l : List A) → Set where -- type \in
  i0 : {x : A} {xs : List A} → x ∈ (x ∷ xs)
  iS : {x y : A} {xs : List A} → x ∈ xs → x ∈ (y ∷ xs) 

mutual
  -- Judgement for values
  data _⊢ⱽ_ (Γ : Ctx) : Typ → Set where
    var : {t : Typ} → t ∈ Γ → Γ ⊢ⱽ t     -- variable
    const : State → Γ ⊢ⱽ TState        -- every s ∈ State is a value of type TState
    ⋆ : Γ ⊢ⱽ unit                      -- unit
    #t : Γ ⊢ⱽ bool                   -- true
    #f : Γ ⊢ⱽ bool                  -- false
    lam : {t₁ t₂ : Typ} → Γ ,, t₁ ⊢ᶜ t₂ → Γ ⊢ⱽ t₁ ⇒ t₂

  -- Judgment for computations
  data _⊢ᶜ_ (Γ : Ctx) : Typ → Set where
    return : {t : Typ} → Γ ⊢ⱽ t → Γ ⊢ᶜ t
    LET_IN_ : {t₁ t₂ : Typ} →  Γ ⊢ⱽ t₁ → Γ ,, t₁ ⊢ᶜ t₂ → Γ ⊢ᶜ t₂
    app : {t₁ t₂ : Typ} → Γ ⊢ⱽ t₁ ⇒ t₂ → Γ ⊢ⱽ t₁ → Γ ⊢ᶜ t₂           
    raise : {t : Typ} → Exceptions → Γ ⊢ᶜ t                            
    get : {t : Typ} → Γ ,, TState ⊢ᶜ t → Γ ⊢ᶜ t
    put : {t : Typ} → Γ ⊢ⱽ TState → Γ ⊢ⱽ t → Γ ⊢ᶜ t


module Semantics where 

  ⟦_⟧ᵗ : Typ → Set  
  ⟦ unit ⟧ᵗ = ⊤
  ⟦ bool ⟧ᵗ = Bool
  ⟦ A ⇒ B ⟧ᵗ = ⟦ A ⟧ᵗ → ⟦ B ⟧ᵗ
  ⟦ TState ⟧ᵗ = State

  ⟦_⟧ᵉ : Ctx → Set
  ⟦ [] ⟧ᵉ = ⊤
  ⟦ t ∷ Γ ⟧ᵉ = ⟦ Γ ⟧ᵉ × ⟦ t ⟧ᵗ

  mutual
    ⟦_⟧ᵛ : {Γ : Ctx} {A : Typ} → Γ ⊢ⱽ A → ⟦ Γ ⟧ᵉ → ⟦ A ⟧ᵗ
    ⟦ var x ⟧ᵛ γ = {!   !}
    ⟦ const x ⟧ᵛ γ = x
    ⟦ ⋆ ⟧ᵛ γ = tt
    ⟦ #t ⟧ᵛ γ = true
    ⟦ #f ⟧ᵛ γ = false
    ⟦ lam e ⟧ᵛ γ = {! λ x → ⟦ e ⟧ᶜ (γ , x) !}

    -- ⟦_⟧ᶜ : {Γ : Ctx} {A : Typ} → Γ ⊢ᶜ A → ⟦ Γ ⟧ᵉ → {!   !}

-- a = Monad.Update.Update

  -- ⟦_⟧ˣ
  -- ⟦ var i0 ⟧ᵛ ( _ , snd) = snd
  -- ⟦ var (iS x) ⟧ᵛ γ = {!   !}
  

  

      