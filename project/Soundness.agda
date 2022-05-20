module Soundness where

import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (refl; sym; trans; cong; cong₂; subst; [_]; inspect) renaming (_≡_ to _`≡_) 
open Eq.≡-Reasoning      using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)

open import Function using (_∘_; id)

open import DefinitionalInterpreter
open import EquationalTheory
open import FGCBV
open import RenamingAndSubstitution
open import ESMonad


-- aux-return-x : {A : Ty} {Γ Γ' : Ctx} {γ : ⟦ Γ' ⟧ᵉ} {s : State} {x : Γ ⊢ᵛ A} {ρ : Ren Γ Γ'} → (⟦ ren-v ρ x ⟧ᵛ γ , s) `≡ (⟦ x ⟧ᵛ (⟦ ρ ⟧ʳ γ) , s)
-- aux-return-x = 
--     begin
--     {!   !}
--     ≡⟨ {!   !} ⟩
--     {!   !}

mutual
    lemma-ren-c : {A : Ty} { Γ Γ' : Ctx} {γ :  ⟦ Γ ⟧ᵉ} {N : Γ ⊢ᶜ A} {ρ : Ren Γ Γ'} → ⟦ ren-c ρ N ⟧ᶜ `≡ (⟦ N ⟧ᶜ ∘ ⟦ ρ ⟧ʳ)

    lemma-ren-c {A = A} {Γ = Γ} {Γ' = Γ'} {γ} {N = return x} {ρ = ρ} = fun-ext (λ γ → fun-ext (λ s → cong inj₂ {!   !}))

    lemma-ren-c {A = A} {Γ = Γ} {Γ' = Γ'} {N = `let N `in N₁} {ρ = ρ} = {!   !}
    lemma-ren-c {A = A} {Γ = Γ} {Γ' = Γ'} {N = app x x₁} {ρ = ρ} = {!   !}
    lemma-ren-c {A = A} {Γ = Γ} {Γ' = Γ'} {N = `raise x} {ρ = ρ} = refl
    lemma-ren-c {A = A} {Γ = Γ} {Γ' = Γ'} {N = `get N} {ρ = ρ} = fun-ext (λ x → {!   !})
    lemma-ren-c {A = A} {Γ = Γ} {Γ' = Γ'} {N = `put x N} {ρ = ρ} = {!   !}  --pattern match on N

    lemma-ren-v : {A : Ty} { Γ Γ' : Ctx} {N : Γ ⊢ᵛ A} {ρ : Ren Γ Γ'} → ⟦ ren-v ρ N ⟧ᵛ `≡ (⟦ N ⟧ᵛ ∘ ⟦ ρ ⟧ʳ)
    lemma-ren-v = {!   !}




soundness : {A : Ty} {Γ : Ctx} {M N : Γ ⊢ᶜ A} → Γ ⊢ᶜ M ≡ N → ⟦ M ⟧ᶜ `≡ ⟦ N ⟧ᶜ

soundness {M = M} {N = N} β-reduction = {!   !} 
soundness let-put = {!   !}
soundness let-get = {!   !}
soundness put-get = fun-ext {!   !}

soundness {A = A} {M = M} {N = N} GET = 
    begin
        ⟦ `get (ren-c S N) ⟧ᶜ
        ≡⟨ lemma-ren-c ⟩
        ⟦ N ⟧ᶜ ∘ id
        ≡⟨ {!   !} ⟩
        {!   !}
           
soundness put-put = refl
soundness raise-put = refl
soundness raise-get = refl
soundness raise-let = refl

soundness return-left = {!   !}
soundness return-right = {!   !}
soundness let-assoc = {!   !} 
    