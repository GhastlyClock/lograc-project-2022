module Monoid where

open import Level        renaming (zero to lzero; suc to lsuc)
import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)

open import Axiom.Extensionality.Propositional using (Extensionality)
postulate fun-ext : ∀ {a b} → Extensionality a b

record Monoid {l} : Set (lsuc l) where
  infixl 7 _·_
  field
    -- carrier type of the monoid
    M       : Set l
    -- identity element (unicode with `\epsilon`)
    ε       : M
    -- binary operation (unicode with `\cdot`)
    _·_     : M → M → M
    -- monoid laws
    ε-left  : (m : M) → ε · m ≡ m
    ε-right : (m : M) → m · ε ≡ m
    ·-assoc : (m₁ m₂ m₃ : M) → (m₁ · m₂) · m₃ ≡ m₁ · (m₂ · m₃)
