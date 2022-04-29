module FGCBV where

open import Data.Nat
open import Data.Bool using (true; false; Bool)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Agda.Builtin.Unit 
open import Data.List using (List; []; _∷_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Level renaming (zero to lzero; suc to lsuc; _⊔_ to _⊔ˡ_)
-- open import Categories.Category
-- open import Categories.Category.Instance.Sets

import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)
open Eq.≡-Reasoning      using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Axiom.Extensionality.Propositional using (Extensionality)

postulate fun-ext : ∀ {a b} → Extensionality a b

-----------------------------------------------------------------------------------------------------
-- A postulate is a declaration of an element of some type without 
-- an accompanying definition. With postulates we can introduce 
-- elements in a type without actually giving the definition of 
-- the element itself.

postulate     -- Think of it as some universal set of states
  State : Set₀
  Exceptions : Set₀


record Monad {l} : Set (lsuc l) where
  field
    -- carrier (object map) fo the Kleisli triple
    T       : Set l → Set l
    -- unit
    η       : {X : Set l} → X → T X
    -- bind
    _>>=_   : {X Y : Set l} → T X → (X → T Y) → T Y
    -- laws
    η-left  : {X Y : Set l} (x : X) (f : X → T Y) → η x >>= f ≡ f x
    η-right : {X : Set l} (c : T X) → c >>= η ≡ c
    >>=-assoc : {X Y Z : Set l} (c : T X) (f : X → T Y) (g : Y → T Z)
              → ((c >>= f) >>= g) ≡ c >>= (λ x → f x >>= g)

ESMonad : Monad {lzero}
ESMonad = record
  { T = λ X → State →  Exceptions ⊎ (X × State)
  ; η = λ x s → inj₂ (x , s)
  ; _>>=_  = _>>=-aux_
  ; η-left = λ X f → refl
  ; η-right = λ m → fun-ext λ s → η-right-aux m s
  ; >>=-assoc = λ c f g → fun-ext (>>=-assoc-aux c f g)
  }
  where
    _>>=-aux_ : {l : Level} {X : Set l} {Y : Set l} → (State → Exceptions ⊎ X × State) → (X → State → Exceptions ⊎ Y × State) → State  → (Exceptions ⊎ Y × State)
    _>>=-aux_ x f s with (x s)
    ... | inj₁ e = inj₁ e
    ... | inj₂ y = f (proj₁ y) (proj₂ y)


    η-right-aux : {l : Level} {X : Set l} → (m : State → Exceptions ⊎ X × State) →  (s : State) → (m >>=-aux (λ x s₁ → inj₂ (x , s₁))) s ≡ m s
    η-right-aux m s with (m s)
    ... | inj₁ e = refl
    ... | inj₂ y = refl

    >>=-assoc-aux : {l : Level} {X Y Z : Set l} → 
                    (c : State → Exceptions ⊎ X × State) → 
                    (f : X → State → Exceptions ⊎ Y × State) → 
                    (g : Y → State → Exceptions ⊎ Z × State) → 
                    (s : State) → 
                    ((c >>=-aux f) >>=-aux g) s ≡ (c >>=-aux (λ x₁ → f x₁ >>=-aux g)) s
    >>=-assoc-aux c f g s with (c s) 
    ... | inj₁ e = refl
    ... | inj₂ y with (f (proj₁ y) (proj₂ y))
    ...           | inj₁ e = refl
    ...           | inj₂ y₁ = refl

open Monad ESMonad 

put : {A : Set} → State → T A → T A
put s f = λ _ → f s

get : {A : Set} → (State → T A) → T A
get f = λ s → f s s

raise : {A : Set} → Exceptions →  T A
raise e = λ x → inj₁ e

-- Types of `λbda calculus:
data Ty : Set where
    unit : Ty                -- unit
    bool : Ty                -- bool   
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
    var : {Γ : Ctx} {A : Ty} →                    -- variable
      A ∈ Γ → 
      -------
      Γ ⊢ᵛ A
    
    const : {Γ : Ctx} →                           -- every s ∈ State is a value of Ty TState
      State → 
      -------
      Γ ⊢ᵛ TState

    ⋆ : {Γ : Ctx} → 
      --------
      Γ ⊢ᵛ unit

    `true : {Γ : Ctx} →  
      --------
      Γ ⊢ᵛ bool

    `false : {Γ : Ctx} →  
      --------
      Γ ⊢ᵛ bool

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
      Γ ⊢ᵛ A → 
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
      Γ ⊢ᵛ A →
      -------------
      Γ ⊢ᶜ A


module Semantics where 

     
  ⟦_⟧ᵗ : Ty → Set
  ⟦ unit ⟧ᵗ = ⊤
  ⟦ bool ⟧ᵗ = Bool
  ⟦ A ⇒ B ⟧ᵗ = ⟦ A ⟧ᵗ → T ⟦ B ⟧ᵗ
  ⟦ TState ⟧ᵗ = State

  ⟦_⟧ᵉ : Ctx → Set
  ⟦ ∅ ⟧ᵉ = ⊤
  ⟦ Γ ,, x ⟧ᵉ = ⟦ Γ ⟧ᵉ × ⟦ x ⟧ᵗ

  -- open Monad ESMonad

  var-aux : {Γ : Ctx} {A : Ty} → (x : A ∈ Γ) → ⟦ Γ ⟧ᵉ → ⟦ A ⟧ᵗ
  var-aux Z γ = proj₂ γ
  var-aux (S x) γ = var-aux x (proj₁ γ)

  mutual

    ⟦_⟧ᵛ : {Γ : Ctx} {A : Ty} → Γ ⊢ᵛ A → ⟦ Γ ⟧ᵉ → ⟦ A ⟧ᵗ
    ⟦ var x ⟧ᵛ γ = var-aux x γ
    ⟦ const x ⟧ᵛ γ = x
    ⟦ ⋆ ⟧ᵛ γ = tt
    ⟦ `true ⟧ᵛ γ = true
    ⟦ `false ⟧ᵛ γ = false
    ⟦ `λ e ⟧ᵛ γ = λ x → ⟦ e ⟧ᶜ (γ , x)


    ⟦_⟧ᶜ : {Γ : Ctx} {A : Ty} → Γ ⊢ᶜ A → ⟦ Γ ⟧ᵉ → T (⟦ A ⟧ᵗ)
    ⟦ return V ⟧ᶜ γ = η (⟦ V ⟧ᵛ γ)
    ⟦ `let V `in M ⟧ᶜ γ = ⟦ M ⟧ᶜ (γ , ⟦ V ⟧ᵛ γ)
    ⟦ app V W ⟧ᶜ γ = ((⟦ V ⟧ᵛ γ) (⟦ W ⟧ᵛ γ))
    ⟦ `get M ⟧ᶜ γ = get λ s → ⟦ M ⟧ᶜ (γ , s)
    ⟦ `put V M ⟧ᶜ γ = put (⟦ V ⟧ᵛ γ) (η (⟦ M ⟧ᵛ γ))
    ⟦ `raise e ⟧ᶜ γ = raise e
  

  

           