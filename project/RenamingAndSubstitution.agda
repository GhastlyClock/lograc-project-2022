module RenamingAndSubstitution where

import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)
open Eq.≡-Reasoning      using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Function using (id; _∘_)

open import FGCBV

module Renaming where
    Ren : Ctx → Ctx → Set
    Ren Γ Γ' = ∀ {A : Ty} → A ∈ Γ → A ∈ Γ'

    id-ren : {Γ : Ctx} → Ren Γ Γ
    id-ren = id

    wk-ren : {Γ : Ctx} {A : Ty} → Ren Γ (Γ ,, A)
    wk-ren p = S p

    ext-ren : {Γ Γ' : Ctx} {A : Ty} → Ren Γ Γ' → A ∈ Γ' → Ren (Γ ,, A) Γ'
    ext-ren ρ p Z = p
    ext-ren ρ p (S dokaz) = ρ dokaz

    exc-ren : {Γ : Ctx} {A B : Ty} → Ren ((Γ ,, A) ,, B)  ((Γ ,, B) ,, A)
    exc-ren Z = S Z
    exc-ren (S Z) = Z
    exc-ren (S (S dokaz)) = S (S dokaz)

    exts-ren : {Γ Γ' : Ctx} {A : Ty} → Ren Γ Γ' → Ren (Γ ,, A) (Γ' ,, A)
    exts-ren ρ Z = Z
    exts-ren ρ (S dokaz) = S (ρ dokaz)

    mutual
        ren-v : {Γ Γ' : Ctx} → Ren Γ Γ' → {A : Ty} → Γ ⊢ᵛ A → Γ' ⊢ᵛ A
        ren-v ρ (var x) = var (ρ x)
        ren-v ρ (const x) = const x
        ren-v ρ ⋆ = ⋆
        ren-v ρ (`λ M) = `λ (ren-c (exts-ren ρ) M)

        ren-c : {Γ Γ' : Ctx} → Ren Γ Γ' → {A : Ty} → Γ ⊢ᶜ A → Γ' ⊢ᶜ A
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

    wk-sub : {Γ : Ctx} {A : Ty} → Sub Γ (Γ ,, A)
    wk-sub dokaz = var (S dokaz)

    ext-sub :  {Γ Γ' : Ctx} {A : Ty} → Sub Γ Γ' → Γ' ⊢ᵛ A → Sub (Γ ,, A) Γ'
    ext-sub σ V Z = V
    ext-sub σ V (S p) = σ p

    exts-sub : {Γ Γ' : Ctx} {A : Ty} → Sub Γ Γ' → Sub (Γ ,, A) (Γ' ,, A)
    exts-sub σ Z = var Z
    exts-sub σ (S x) = ren-v wk-ren (σ x)

    mutual
        sub-v : {Γ Γ' : Ctx} → Sub Γ Γ' → {A : Ty} → Γ ⊢ᵛ A → Γ' ⊢ᵛ A
        sub-v σ (var x) = σ x
        sub-v σ (const x) = const x
        sub-v σ ⋆ = ⋆
        sub-v σ (`λ M) = `λ (sub-c (exts-sub σ) M)

        sub-c : {Γ Γ' : Ctx} → Sub Γ Γ' → {A : Ty} → Γ ⊢ᶜ A → Γ' ⊢ᶜ A
        sub-c σ (return V) = return (sub-v σ V)
        sub-c σ (`let M `in N) = `let sub-c σ M `in sub-c (exts-sub σ) N
        sub-c σ (app V W) = app (sub-v σ V) (sub-v σ W)
        sub-c σ (`raise E) = `raise E
        sub-c σ (`get M) = `get (sub-c (exts-sub σ) M)
        sub-c σ (`put V M) = `put (sub-v σ V) (sub-c σ M)

open Substitution public

lemma-ren-sub : ∀ {Γ Γ' : Ctx} → Ren Γ Γ' → Sub Γ Γ'
lemma-ren-sub ρ = var ∘ ρ

_[_] : ∀ {Γ A B} → (Γ ,, B) ⊢ᶜ A → Γ ⊢ᵛ B → Γ ⊢ᶜ A
_[_] {Γ} {B = B} M V = sub-c (ext-sub id-sub V) M