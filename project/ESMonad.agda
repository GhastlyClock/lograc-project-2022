module ESMonad where

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