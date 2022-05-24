module RenamingAndSubstitution where

import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)
open Eq.≡-Reasoning      using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Function using (id)

open import FGCBV

module Renaming where
    Ren : Ctx → Ctx → Set
    Ren Γ Γ' = ∀ {A : Ty} → A ∈ Γ → A ∈ Γ'

    id-ren : {Γ : Ctx} → Ren Γ Γ
    id-ren = id

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

        ren-c : ∀ {Γ Γ' : Ctx} → ∀ {A : Ty} → Ren Γ Γ' → Γ ⊢ᶜ A → Γ' ⊢ᶜ A
        ren-c ρ (return V) = return (ren-v ρ V)
        ren-c ρ (`let M `in N) = `let ren-c ρ M `in ren-c (exts-ren ρ) N
        ren-c ρ (app V W) = app (ren-v ρ V) (ren-v ρ W)
        ren-c ρ (`raise E) = `raise E
        ren-c ρ (`get M) = `get (ren-c (exts-ren ρ) M)
        ren-c ρ (`put V M) = `put (ren-v ρ V) (ren-c ρ M)

open Renaming public


module Substitution where
    Sub : Ctx → Ctx → Set
    Sub Γ Γ' = ∀ {A} → A ∈ Γ → Γ' ⊢ᵛ A

    id-sub : {Γ : Ctx} → Sub Γ Γ
    id-sub = var 

    wk-sub : ∀ {Γ A} → Sub Γ (Γ ,, A)
    wk-sub dokaz = var (S dokaz)

    ext-sub :  ∀ {Γ Γ' A} → Sub Γ Γ' → Γ' ⊢ᵛ A → Sub (Γ ,, A) Γ'
    ext-sub σ V Z = V
    ext-sub σ V (S p) = σ p

    exts-sub : ∀ {Γ Γ' A} → Sub Γ Γ' → Sub (Γ ,, A) (Γ' ,, A)
    exts-sub σ Z = var Z
    exts-sub σ (S x) = ren-v wk-ren (σ x)

    mutual
        sub-v : ∀ {Γ Γ' A} → Sub Γ Γ' → Γ ⊢ᵛ A → Γ' ⊢ᵛ A
        sub-v σ (var x) = σ x
        sub-v σ (const x) = const x
        sub-v σ ⋆ = ⋆
        sub-v σ `true = `true
        sub-v σ `false = `false
        sub-v σ (`λ M) = `λ (sub-c (exts-sub σ) M)

        sub-c : ∀ {Γ Γ' A} → Sub Γ Γ' → Γ ⊢ᶜ A → Γ' ⊢ᶜ A
        sub-c σ (return V) = return (sub-v σ V)
        sub-c σ (`let M `in N) = `let sub-c σ M `in sub-c (exts-sub σ) N
        sub-c σ (app V W) = app (sub-v σ V) (sub-v σ W)
        sub-c σ (`raise E) = `raise E
        sub-c σ (`get M) = `get (sub-c (exts-sub σ) M)
        sub-c σ (`put V M) = `put (sub-v σ V) (sub-c σ M)

open Substitution public

lemma-ren-sub : ∀ {Γ Γ' : Ctx} → Ren Γ Γ' → Sub Γ Γ'
lemma-ren-sub ρ = λ z → var (ρ z)

σ-aux : ∀ {Γ B} → (V : Γ ⊢ᵛ B) → Sub (Γ ,, B) Γ
σ-aux V Z = V
σ-aux _ (S p) = var p

_[_] : ∀ {Γ A B} → (Γ ,, B) ⊢ᶜ A → Γ ⊢ᵛ B → Γ ⊢ᶜ A
_[_] {Γ} {B = B} M V = sub-c (σ-aux V) M