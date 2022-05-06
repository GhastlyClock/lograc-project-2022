module RenamingAndSubstitution where


-- open import Data.Nat
-- open import Data.Bool using (true; false; Bool)
-- open import Data.Product using (_×_; _,_; proj₁; proj₂)

-- open import Agda.Builtin.Unit 
-- open import Data.List using (List; []; _∷_)
-- open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
-- open import Level renaming (zero to lzero; suc to lsuc; _⊔_ to _⊔ˡ_)
-- -- open import Categories.Category
-- -- open import Categories.Category.Instance.Sets

-- import Relation.Binary.PropositionalEquality as Eq
-- open Eq                  using (_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)
-- open Eq.≡-Reasoning      using (begin_; _≡⟨⟩_; step-≡; _∎)

-- open import Axiom.Extensionality.Propositional using (Extensionality)

-- postulate fun-ext : ∀ {a b} → Extensionality a b


open import FGCBV

module Renaming where
    extend-renaming : {Γ Δ : Ctx}
        → ({A : Ty} → A ∈ Γ → A ∈ Δ)
        -----------------------------------------
        → {A B : Ty} → A ∈ (Γ ,, B) → A ∈ (Δ ,, B)
    extend-renaming ρ Z = Z
    extend-renaming ρ (S x) = {!   !}


    rename-v : {Γ Δ : Ctx}
        → ({A : Ty} → A ∈ Γ → A ∈ Δ)
            ---------------------------
        → {A : Ty} → Γ ⊢ᵛ A → Δ ⊢ᵛ A
    rename-v = {!   !}

    rename-c : {Γ Δ : Ctx}
        → ({A : Ty} → A ∈ Γ → A ∈ Δ)
            ---------------------------
        → {A : Ty} → Γ ⊢ᶜ A → Δ ⊢ᶜ A
    rename-c = {!   !}

module Substitution where
    extend-subst : {Γ Δ : Ctx}
        → ({A : Ty} → A ∈ Γ → Δ ⊢ᵛ A)
            ---------------------------------------
        → {A B : Ty} → A ∈ (Γ ,, B) → (Δ ,, B) ⊢ᵛ A
    extend-subst = {!   !}

    subst-v : {Γ Δ : Ctx}
        → ({A : Ty} → A ∈ Γ → Δ ⊢ᵛ A)
            -------------------------
        → {A : Ty} → Γ ⊢ᵛ A → Δ ⊢ᵛ A
    subst-v = {!   !}


    subst-c : {Γ Δ : Ctx}
        → ({A : Ty} → A ∈ Γ → Δ ⊢ᵛ A)
            -------------------------
        → {A : Ty} → Γ ⊢ᶜ A → Δ ⊢ᶜ A
    subst-c = {!   !}
        