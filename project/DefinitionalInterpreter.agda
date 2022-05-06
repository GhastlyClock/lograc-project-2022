module DefinitionalInterpreter where

open import Data.Bool using (true; false; Bool)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Agda.Builtin.Unit 

open import FGCBV
open import ESMonad

open Monad ESMonad
     
⟦_⟧ᵗ : Ty → Set
⟦ unit ⟧ᵗ = ⊤
⟦ bool ⟧ᵗ = Bool
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