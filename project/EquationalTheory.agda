module EquationalTheory where

open import RenamingAndSubstitution

open import FGCBV
open import ESMonad using (Exceptions)

data _⊢ᵛ_≡_ : {A : Ty} → (Γ : Ctx) → Γ ⊢ᵛ A  → Γ ⊢ᵛ A → Set where
    η-reduction : {Γ : Ctx} {A B : Ty} → (V : Γ ⊢ᵛ (A ⇒ B)) →
        -----------------------------------------
        Γ ⊢ᵛ V ≡ `λ (app (sub-v wk-sub V) (var Z))

data _⊢ᶜ_≡_ : {A : Ty} → (Γ : Ctx) → Γ ⊢ᶜ A  → Γ ⊢ᶜ A → Set where
    β-reduction : {Γ : Ctx} {A B : Ty} {M : (Γ ,, A) ⊢ᶜ B} {V : Γ ⊢ᵛ A} → 
        -------------------------------------------------------
        Γ ⊢ᶜ app (`λ M) V ≡ (M [ V ])
        
    let-put : {Γ : Ctx} {A B : Ty} {V : Γ ⊢ᵛ TState} {M : Γ ⊢ᶜ A} {N : Γ ,, A ⊢ᶜ B} →
        ---------------------------------------------------------------------------
        Γ ⊢ᶜ `let `put V M `in N ≡ `put V (`let M `in N)
    
    -- let-get : {Γ : Ctx} {A B : Ty} {V : Γ ⊢ᵛ TState} {M : Γ ⊢ᶜ A} {N : Γ ,, A ⊢ᶜ B} →
    --     ---------------------------------------------------------------------------
    --     Γ ⊢ᶜ `let `put V M `in N ≡ `put V (`let M `in N)
    putget : {Γ : Ctx} {A : Ty} {V : Γ ⊢ᵛ TState} {M : Γ ⊢ᶜ A} → 
        --------------------------------------------------------------
        Γ ⊢ᶜ `let `put V M `in `get {!   !} ≡ {!   !}
        -- Γ ⊢ᶜ `let {! η-reduction  !} `in N ≡ `put V (`let {!   !} `in N)
    -- -- η-put : {Γ : Ctx} {A : Ty} {V : Γ ⊢ᵛ TState} {M : Γ ⊢ᶜ A} →
    -- --     -----------------------------------------
    -- --     Γ ⊢ᶜ M ≡ `put V M
    raise-put : {Γ : Ctx} {A B : Ty} {V : Γ ⊢ᵛ TState} {E : Exceptions} {M : Γ ,, A ⊢ᶜ B} → 
        ------------------------------------------------
        Γ ⊢ᶜ `let (`put V (`raise E)) `in M ≡ `raise E
    -- -- raise-get : {Γ : Ctx} {A : Ty} {V : Γ ⊢ᵛ TState} {E : Exceptions} {M : Γ ⊢ᶜ A} →
    -- --     ------------------------------------------------
    -- --     Γ ⊢ᶜ `raise E ≡ (`let M `in `get (`raise E) )
    


module AlgebraicEquations where