module EquationalTheory where

open import RenamingAndSubstitution

open import FGCBV
open import ESMonad using (Exceptions)


data _⊢ᵛ_≡_ : {A : Ty} → (Γ : Ctx) → Γ ⊢ᵛ A  → Γ ⊢ᵛ A → Set where
    η-reduction : {Γ : Ctx} {A B : Ty} → {V : Γ ⊢ᵛ (A ⇒ B)} →
        -----------------------------------------
        Γ ⊢ᵛ V ≡ `λ (app (sub-v wk-sub V) (var Z))

data _⊢ᶜ_≡_ : {A : Ty} → (Γ : Ctx) → Γ ⊢ᶜ A  → Γ ⊢ᶜ A → Set where

    β-reduction : {Γ : Ctx} {A B : Ty} → {M : (Γ ,, A) ⊢ᶜ B} {V : Γ ⊢ᵛ A} → 
        -------------------------------------------------------
        Γ ⊢ᶜ app (`λ M) V ≡ (M [ V ])


        
    let-put : {Γ : Ctx} {A B : Ty} {V : Γ ⊢ᵛ TState} {M : Γ ⊢ᶜ A} {N : Γ ,, A ⊢ᶜ B} →
        ---------------------------------------------------------------------------
        Γ ⊢ᶜ `let `put V M `in N ≡ `put V (`let M `in N)

    let-get : {Γ : Ctx} {A B : Ty} {M : Γ ,, TState ⊢ᶜ A} {N : Γ ,, A ⊢ᶜ B} →
        ---------------------------------------------------------------------------
        Γ ⊢ᶜ `let `get M `in N  ≡ `get (`let M `in ren-c (exts-ren wk-ren) N)

    put-get : {Γ : Ctx} {A B : Ty} {V : Γ ⊢ᵛ TState} {M : Γ ,, TState ⊢ᶜ A}  → 
        ---------------------------------------------------------------------------
        Γ  ⊢ᶜ `put V (`get M) ≡ `put V (M [ V ])

    GET : {Γ : Ctx} {A : Ty} {M : Γ ⊢ᶜ A} →
        ---------------------------------------------------------------------------
        Γ ⊢ᶜ `get (ren-c S M)  ≡  M

    put-put : {Γ : Ctx} {A : Ty} {V W : Γ ⊢ᵛ TState} {M : Γ ⊢ᶜ A} →
        ----------------------------------------------------------------------------
        Γ ⊢ᶜ `put V (`put W M)  ≡ `put W M

    raise-put : {Γ : Ctx} {A : Ty} {V : Γ ⊢ᵛ TState} {E : Exceptions} → 
        ------------------------------------------------
        Γ ⊢ᶜ `put V (`raise E) ≡ `raise {Γ} {A} E

    raise-get : {Γ : Ctx} {A : Ty} {V : Γ ⊢ᵛ TState} {E : Exceptions} →
        ---------------------------------------------------------------------------
        Γ ⊢ᶜ `get (`raise E) ≡ `raise {Γ} {A} E

    raise-let : {Γ : Ctx} {A B : Ty} {V : Γ ⊢ᵛ TState} {E : Exceptions} {M : Γ ,, A ⊢ᶜ B} →
        ----------------------------------------------------------------------------
        Γ ⊢ᶜ `let `raise E `in M ≡ `raise E



    return-left :  {Γ : Ctx} {A B : Ty} {V : Γ ⊢ᵛ A} {M : Γ ,, A ⊢ᶜ B} →
        ---------------------------------------------------------------------------
        Γ ⊢ᶜ `let return V `in M ≡ (M [ V ])

    return-right :  {Γ : Ctx} {A B : Ty} {V : Γ ⊢ᵛ A} {M : Γ ⊢ᶜ A} →
        ---------------------------------------------------------------------------
        Γ ⊢ᶜ `let M `in return (var Z) ≡ M

    let-assoc :  {Γ : Ctx} {A B C : Ty} {M : Γ ⊢ᶜ A} {N : Γ ,, A ⊢ᶜ B} {O : Γ ,, B ⊢ᶜ C} →
        ---------------------------------------------------------------------------
        Γ ⊢ᶜ `let ( `let M `in N ) `in O ≡ (`let M `in (`let N `in ren-c (exts-ren S) O))

    
     