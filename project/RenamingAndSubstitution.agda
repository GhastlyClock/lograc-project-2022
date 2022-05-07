module RenamingAndSubstitution where

import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)
open Eq.≡-Reasoning      using (begin_; _≡⟨⟩_; step-≡; _∎)


open import FGCBV

module Renaming where
    Ren : Ctx → Ctx → Set
    Ren Γ Γ' = ∀ {A : Ty} → A ∈ Γ → A ∈ Γ'

    wk-ren : ∀ {Γ A} → Ren Γ (Γ ,, A)
    wk-ren p = S p

    ext-ren : ∀ {Γ Γ' A} → A ∈ Γ' → Ren Γ Γ' → Ren (Γ ,, A) Γ'
    ext-ren x ρ Z = x
    ext-ren x ρ (S dokaz) = ρ dokaz

    exc-ren : ∀ {Γ A B} → Ren ((Γ ,, A) ,, B)  ((Γ ,, B) ,, A)
    exc-ren Z = S Z
    exc-ren (S Z) = Z
    exc-ren (S (S dokaz)) = S (S dokaz)

    exts-ren : ∀ {Γ Γ' A} → Ren Γ Γ' → Ren (Γ ,, A) (Γ' ,, A)
    exts-ren ρ Z = Z
    exts-ren ρ (S dokaz) = S (ρ dokaz)

    mutual
        ren-v : ∀ {Γ Γ' : Ctx} → ∀ {A : Ty} → Ren Γ Γ' → Γ ⊢ᵛ A → Γ' ⊢ᵛ A
        ren-v ρ (var x) = var (ρ x)
        ren-v ρ (const x) = const x
        ren-v ρ ⋆ = ⋆
        ren-v ρ `true = `true
        ren-v ρ `false = `false
        ren-v ρ (`λ M) = `λ (ren-c (exts-ren ρ) M)
        -- ren-v ρ (`λ M) = `λ (ren-c {!   !}  M)

        ren-c : ∀ {Γ Γ' : Ctx} → ∀ {A : Ty} → Ren Γ Γ' → Γ ⊢ᶜ A → Γ' ⊢ᶜ A
        ren-c ρ (return V) = return (ren-v ρ V)
        ren-c ρ (`let V `in M) = `let (ren-v ρ V) `in ren-c (exts-ren ρ) M
        ren-c ρ (app V W) = app (ren-v ρ V) (ren-v ρ W)
        ren-c ρ (`raise E) = `raise E
        ren-c ρ (`get M) = `get (ren-c (exts-ren ρ) M)
        ren-c ρ (`put V W) = `put (ren-v ρ V) (ren-v ρ W)

open Renaming


module Substitution where
    Sub : Ctx → Ctx → Set
    Sub Γ Γ' = ∀ {A} → A ∈ Γ → Γ' ⊢ᵛ A

    wk-sub : ∀ {Γ A} → Sub Γ (Γ ,, A)
    wk-sub dokaz = var (S dokaz)

    ext-sub :  ∀ {Γ Γ' A} → A ∈ Γ' → Sub Γ Γ' → Sub (Γ ,, A) Γ'
    ext-sub x ρ Z = var x
    ext-sub x ρ (S dokaz) = ρ dokaz


    exts-sub : ∀ {Γ Γ' A} → Sub Γ Γ' → Sub (Γ ,, A) (Γ' ,, A)
    exts-sub ρ Z = var Z
    exts-sub ρ (S x) = ren-v wk-ren (ρ x)

    mutual
        sub-v : ∀ {Γ Γ' A} → Sub Γ Γ' → Γ ⊢ᵛ A → Γ' ⊢ᵛ A
        sub-v ρ (var x) = ρ x
        sub-v ρ (const x) = const x
        sub-v ρ ⋆ = ⋆
        sub-v ρ `true = `true
        sub-v ρ `false = `false
        sub-v ρ (`λ M) = `λ (sub-c (exts-sub ρ) M)

        sub-c : ∀ {Γ Γ' A} → Sub Γ Γ' → Γ ⊢ᶜ A → Γ' ⊢ᶜ A
        sub-c ρ (return V) = return (sub-v ρ V)
        sub-c ρ (`let V `in M) = `let sub-v ρ V `in sub-c (exts-sub ρ) M
        sub-c ρ (app V W) = app (sub-v ρ V) (sub-v ρ W)
        sub-c ρ (`raise E) = `raise E
        sub-c ρ (`get M) = `get (sub-c (exts-sub ρ) M)
        sub-c ρ (`put V W) = `put (sub-v ρ V) (sub-v ρ W)

open Substitution

enakost : ∀ {Γ Γ' : Ctx} → Ren Γ Γ'  → Sub Γ Γ'
enakost dokaz = λ x → var (dokaz x)

_[_] : ∀ {Γ A B} → (Γ ,, B) ⊢ᶜ A → Γ ⊢ᵛ B → Γ ⊢ᶜ A
_[_] {Γ} {B = B} M V = sub-c σ M
  where
    σ : ∀ {A : Ty} → A ∈ (Γ ,, B) → Γ ⊢ᵛ A
    σ Z = V
    σ (S x) = var x