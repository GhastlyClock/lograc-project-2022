module DefinitionalInterpreter where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Agda.Builtin.Unit 

open import Function

open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)

open import FGCBV
open import ESMonad
open import RenamingAndSubstitution


⟦_⟧ᵗ : Ty → Set
⟦ unit ⟧ᵗ = ⊤
⟦ A ⇒ B ⟧ᵗ = ⟦ A ⟧ᵗ → T ⟦ B ⟧ᵗ
⟦ TState ⟧ᵗ = State

⟦_⟧ᵉ : Ctx → Set
⟦ ∅ ⟧ᵉ = ⊤
⟦ Γ ,, x ⟧ᵉ = ⟦ Γ ⟧ᵉ × ⟦ x ⟧ᵗ

var-aux : {Γ : Ctx} {A : Ty} → (x : A ∈ Γ) → ⟦ Γ ⟧ᵉ → ⟦ A ⟧ᵗ
var-aux Z γ = proj₂ γ
var-aux (S x) γ = var-aux x (proj₁ γ)


mutual

    ⟦_⟧ᵛ : {Γ : Ctx} {A : Ty} → Γ ⊢ᵛ A → ⟦ Γ ⟧ᵉ → ⟦ A ⟧ᵗ
    ⟦ var x ⟧ᵛ γ = var-aux x γ
    ⟦ const x ⟧ᵛ γ = x
    ⟦ ⋆ ⟧ᵛ γ = tt
    ⟦ `λ e ⟧ᵛ γ = λ x → ⟦ e ⟧ᶜ (γ , x)


    ⟦_⟧ᶜ : {Γ : Ctx} {A : Ty} → Γ ⊢ᶜ A → ⟦ Γ ⟧ᵉ → T (⟦ A ⟧ᵗ)
    ⟦ return V ⟧ᶜ γ = η (⟦ V ⟧ᵛ γ)
    ⟦ `let M `in N ⟧ᶜ γ = λ s → letin-aux M N γ s
    ⟦ app V W ⟧ᶜ γ = ((⟦ V ⟧ᵛ γ) (⟦ W ⟧ᵛ γ))
    ⟦ `get M ⟧ᶜ γ = get λ s → ⟦ M ⟧ᶜ (γ , s)
    ⟦ `put V M ⟧ᶜ γ = put (⟦ V ⟧ᵛ γ) (⟦ M ⟧ᶜ γ)
    ⟦ `raise e ⟧ᶜ γ = raise e
    
    letin-aux : {Γ : Ctx} {A B : Ty} → Γ ⊢ᶜ A → Γ ,, A ⊢ᶜ B → ⟦ Γ ⟧ᵉ → State → Exceptions ⊎ (⟦ B ⟧ᵗ × State)
    letin-aux M N γ s with (⟦ M ⟧ᶜ γ) s
    ... | inj₁ e = inj₁ e
    ... | inj₂ v = ⟦ N ⟧ᶜ (γ , proj₁ v) (proj₂ v)



⟦_⟧ʳ : {Γ Γ' : Ctx} → Ren Γ Γ' → ⟦ Γ' ⟧ᵉ → ⟦ Γ ⟧ᵉ
⟦_⟧ʳ {Γ = ∅} {Γ' = Γ'} ρ γ = tt
⟦_⟧ʳ {Γ = Γ ,, A} {Γ' = Γ'} ρ γ = ⟦ ρ ∘ S ⟧ʳ γ , var-aux (ρ Z) γ


⟦_⟧ˢ : {Γ Γ' : Ctx} → Sub Γ Γ' → ⟦ Γ' ⟧ᵉ → ⟦ Γ ⟧ᵉ
⟦_⟧ˢ {Γ = ∅} {Γ' = Γ'} σ γ = tt
⟦_⟧ˢ {Γ = Γ ,, A} {Γ' = Γ'} σ γ = (⟦ σ ∘ S ⟧ˢ γ) , ⟦ σ Z ⟧ᵛ γ

