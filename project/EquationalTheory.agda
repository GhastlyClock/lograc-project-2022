module EquationalTheory where

open import RenamingAndSubstitution

open import FGCBV

data _⊢ᶜ_≡_ : {A : Ty} → (Γ : Ctx) → Γ ⊢ᶜ A  → Γ ⊢ᶜ A → Set where
    β-reduction : {Γ : Ctx} {A B : Ty} {M : (Γ ,, A) ⊢ᶜ B} {V : Γ ⊢ᵛ A} → 
        -------------------------------------------------------
        Γ ⊢ᶜ app (`λ M) V ≡ (M [ V ])
    
data _⊢ᵛ_≡_ : {A : Ty} → (Γ : Ctx) → Γ ⊢ᵛ A  → Γ ⊢ᵛ A → Set where
    η-reduction : {Γ : Ctx} {A B : Ty} → (V : Γ ⊢ᵛ (A ⇒ B)) →
        -----------------------------------------
        Γ ⊢ᵛ V ≡ `λ (app (sub-v wk-sub V) (var Z))


module AlgebraicEquations where