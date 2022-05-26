module FGCBV where

open import ESMonad using (State; Exceptions)


-- Types of lambda calculus:
data Ty : Set where
    unit : Ty                -- unit  
    _⇒_ : Ty → Ty → Ty    -- function
    TState : Ty              -- State

data Ctx : Set where
  ∅ : Ctx
  _,,_ : Ctx → Ty → Ctx
  
-- Precendence
infixr 10 _⇒_
infixr 9 _,,_
infixr 8 _⊢ᵛ_
infixr 8 _⊢ᶜ_

-- de Bruijn indices
data _∈_ : Ty → Ctx → Set where
    Z : {A : Ty} {Γ : Ctx} → A ∈ (Γ ,, A)
    S : {A B : Ty} {Γ : Ctx} → A ∈ Γ → A ∈ (Γ ,, B)
    
mutual
  -- Judgements for values
  data _⊢ᵛ_ : Ctx → Ty → Set where
    var : {Γ : Ctx} {A : Ty} → 
      A ∈ Γ → 
      -------
      Γ ⊢ᵛ A
    
    const : {Γ : Ctx} →
      State → 
      -------
      Γ ⊢ᵛ TState

    ⋆ : {Γ : Ctx} → 
      --------
      Γ ⊢ᵛ unit

    `λ : {Γ : Ctx} {A B : Ty} → 
      Γ ,, A ⊢ᶜ B →
      -------------
      Γ ⊢ᵛ A ⇒ B


  data _⊢ᶜ_ : Ctx → Ty → Set where
    return : {Γ : Ctx} {A : Ty} → 
      Γ ⊢ᵛ A → 
      --------
      Γ ⊢ᶜ A

    `let_`in_ : {Γ : Ctx} {A B : Ty} →  
      Γ ⊢ᶜ A → 
      Γ ,, A ⊢ᶜ B → 
      -------------
      Γ ⊢ᶜ B

    app : {Γ : Ctx} {A B : Ty} → 
      Γ ⊢ᵛ A ⇒ B → 
      Γ ⊢ᵛ A → 
      ------------
      Γ ⊢ᶜ B  

    `raise : {Γ : Ctx} {A : Ty} → 
      Exceptions → 
      ------------
      Γ ⊢ᶜ A

    `get : {Γ : Ctx} {A : Ty} → 
      Γ ,, TState ⊢ᶜ A → 
      -----------------
      Γ ⊢ᶜ A

    `put : {Γ : Ctx} {A : Ty} → 
      Γ ⊢ᵛ TState →
      Γ ⊢ᶜ A →
      -------------
      Γ ⊢ᶜ A
