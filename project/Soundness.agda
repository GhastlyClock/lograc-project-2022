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

---------------------------------------------
------------ ADDITIONAL LEMMAS --------------
---------------------------------------------


-------------------
----- Renaming
-------------------

⟦S∘ρ⟧ʳ-lemma : {Γ Γ' : Ctx} → (ρ : Ren Γ Γ') → (γ' : ⟦ Γ' ⟧ᵉ) → ∀ {A : Ty} {a : ⟦ A ⟧ᵗ} → ⟦ S ∘ ρ ⟧ʳ (γ' , a) `≡ ⟦ ρ ⟧ʳ γ'
⟦S∘ρ⟧ʳ-lemma {Γ = ∅} ρ γ' = refl
⟦S∘ρ⟧ʳ-lemma {Γ = Γ ,, x} ρ γ' = cong (λ f → ( f , var-aux (ρ Z) γ' )) (⟦S∘ρ⟧ʳ-lemma (ρ ∘ S) γ')

⟦id⟧ʳ-lemma : {Γ : Ctx} → (γ : ⟦ Γ ⟧ᵉ) → ⟦ id ⟧ʳ γ `≡ γ
⟦id⟧ʳ-lemma {Γ = ∅} γ = refl
⟦id⟧ʳ-lemma {Γ = Γ ,, A} γ = 
    begin
        (⟦ id ∘ S ⟧ʳ γ , proj₂ γ)
        ≡⟨ refl ⟩
        (⟦ S ∘ id ⟧ʳ γ , proj₂ γ)
        ≡⟨ cong (λ f → (f , proj₂ γ)) (⟦S∘ρ⟧ʳ-lemma id (proj₁ γ)) ⟩
        (⟦ id ⟧ʳ (proj₁ γ) , proj₂ γ)
        ≡⟨ cong (λ f → (f , proj₂ γ)) (⟦id⟧ʳ-lemma (proj₁ γ)) ⟩
        (proj₁ γ , proj₂ γ)
        ≡⟨ refl ⟩
        γ
        ∎

⟦S⟧ʳ-lema : {A : Ty} {Γ : Ctx} → ∀ {γ : ⟦ Γ ⟧ᵉ} {a : ⟦ A ⟧ᵗ} → ⟦ S ⟧ʳ (γ , a) `≡ γ
⟦S⟧ʳ-lema {γ = γ} {a = a} = 
    begin
        ⟦ S ⟧ʳ (γ , a)
        ≡⟨ refl ⟩
        ⟦ (λ x → S (id x)) ⟧ʳ (γ , a)
        ≡⟨ ⟦S∘ρ⟧ʳ-lemma id γ ⟩
        ⟦ id ⟧ʳ γ
        ≡⟨ ⟦id⟧ʳ-lemma γ ⟩
        γ
        ∎

var-aux-lemma : {A : Ty} {Γ Γ' : Ctx} → (ρ : Ren Γ Γ') → (x : A ∈ Γ) → (γ' : ⟦ Γ' ⟧ᵉ) → var-aux (ρ x) γ' `≡ var-aux x (⟦ ρ ⟧ʳ γ')
var-aux-lemma ρ Z γ' = refl
var-aux-lemma ρ (S x) γ' = var-aux-lemma (ρ ∘ S) x γ'

mutual
    lemma-ren-c : {A : Ty} {Γ Γ' : Ctx} → (ρ : Ren Γ Γ') → (M : Γ ⊢ᶜ A) → ⟦ ren-c ρ M ⟧ᶜ `≡ (⟦ M ⟧ᶜ ∘ ⟦ ρ ⟧ʳ)
    
    lemma-ren-c {A = A} {Γ = Γ} {Γ' = Γ'} ρ (return V) = fun-ext (λ γ → fun-ext (λ s → cong (λ x → inj₂ ( x , s )) (lemma-ren-c-return-aux γ V)))
        where
            lemma-ren-c-return-aux : (γ' : ⟦ Γ' ⟧ᵉ) → (V : Γ ⊢ᵛ A) →  ⟦ ren-v ρ V ⟧ᵛ γ' `≡ ⟦ V ⟧ᵛ (⟦ ρ ⟧ʳ γ')
            lemma-ren-c-return-aux γ' (var x) = var-aux-lemma ρ x γ'
            lemma-ren-c-return-aux γ' (const x) = refl
            lemma-ren-c-return-aux γ' ⋆ = refl
            lemma-ren-c-return-aux γ' (`λ M) = fun-ext (λ a → fun-ext (λ s → cong (λ f → (((f γ') a) s)) (lemma-ren-v ρ (`λ M))))

    lemma-ren-c {A = A} {Γ = Γ} {Γ' = Γ'} ρ (`let V `in M) = fun-ext (λ γ → fun-ext (λ s → lemma-ren-c-letin-aux γ s))
        where
            lemma-ren-c-letin-aux : (γ : ⟦ Γ' ⟧ᵉ) → (s : State) → ⟦ ren-c ρ (`let V `in M) ⟧ᶜ γ s `≡ (⟦ `let V `in M ⟧ᶜ ∘ ⟦ ρ ⟧ʳ) γ s
            lemma-ren-c-letin-aux γ s rewrite (lemma-ren-c ρ V) with (⟦ V ⟧ᶜ (⟦ ρ ⟧ʳ γ) s)
            ... | inj₁ e = refl
            ... | inj₂ v = cong (λ f → f (proj₂ v)) pomozen-dokaz
                where
                    pomozen-dokaz : ⟦ ren-c (exts-ren ρ) M ⟧ᶜ (γ , proj₁ v) `≡ ⟦ M ⟧ᶜ (⟦ ρ ⟧ʳ γ , proj₁ v)
                    pomozen-dokaz = 
                        begin
                            ⟦ ren-c (exts-ren ρ) M ⟧ᶜ (γ , proj₁ v)
                            ≡⟨ cong (λ f → f (γ , proj₁ v)) (lemma-ren-c (exts-ren ρ) M) ⟩
                            (⟦ M ⟧ᶜ ∘ ⟦ exts-ren ρ ⟧ʳ) (γ , proj₁ v)
                            ≡⟨ cong (λ f → ⟦ M ⟧ᶜ (f , proj₁ v)) (⟦S∘ρ⟧ʳ-lemma ρ γ) ⟩
                            ⟦ M ⟧ᶜ (⟦ ρ ⟧ʳ γ , proj₁ v)
                            ∎

    lemma-ren-c ρ (app V W) = fun-ext (λ γ → cong₂ (λ f g → (f γ) (g γ)) (lemma-ren-v ρ V) (lemma-ren-v ρ W))

    lemma-ren-c ρ (`raise e) = refl

    lemma-ren-c {A = A} {Γ = Γ} {Γ' = Γ'} ρ (`get M) = fun-ext (λ γ → fun-ext (λ s → cong (λ f → f s) (pomozen-dokaz γ s) ))
        where
            pomozen-dokaz : (γ : ⟦ Γ' ⟧ᵉ) → (s : State) → ⟦ ren-c (exts-ren ρ) M ⟧ᶜ (γ , s) `≡ ⟦ M ⟧ᶜ (⟦ ρ ⟧ʳ γ , s)
            pomozen-dokaz γ s = 
                begin
                    ⟦ ren-c (exts-ren ρ) M ⟧ᶜ (γ , s)
                    ≡⟨ cong (λ f → f (γ , s)) (lemma-ren-c (exts-ren ρ) M) ⟩
                    (⟦ M ⟧ᶜ ∘ ⟦ exts-ren ρ ⟧ʳ) (γ , s)
                    ≡⟨ cong (λ f → ⟦ M ⟧ᶜ (f , s)) (⟦S∘ρ⟧ʳ-lemma ρ γ) ⟩
                    ⟦ M ⟧ᶜ (⟦ ρ ⟧ʳ γ , s)
                    ∎

    lemma-ren-c ρ (`put s M) = fun-ext (λ γ → fun-ext (λ _ → cong₂ (λ f g → (f γ) (g γ)) (lemma-ren-c ρ M) (lemma-ren-v ρ s)))


    lemma-ren-v : {A : Ty} {Γ Γ' : Ctx} → (ρ : Ren Γ Γ') → (V : Γ ⊢ᵛ A) → ⟦ ren-v ρ V ⟧ᵛ `≡ (⟦ V ⟧ᵛ ∘ ⟦ ρ ⟧ʳ)
    lemma-ren-v ρ (var x) = fun-ext λ γ → var-aux-lemma ρ x γ
    lemma-ren-v ρ (const x) = refl
    lemma-ren-v ρ ⋆ = refl
    lemma-ren-v {A = A} {Γ = Γ} {Γ' = Γ'} ρ (`λ M) = fun-ext (λ γ' → fun-ext (λ a → (begin
                                                                                        ⟦ ren-c (exts-ren ρ) M ⟧ᶜ (γ' , a)
                                                                                        ≡⟨ cong (λ f → f (γ' , a)) (lemma-ren-c (exts-ren ρ) M) ⟩
                                                                                        (⟦ M ⟧ᶜ ∘ ⟦ exts-ren ρ ⟧ʳ) (γ' , a)
                                                                                        ≡⟨ cong (λ f → ⟦ M ⟧ᶜ (f , a)) (⟦S∘ρ⟧ʳ-lemma ρ γ') ⟩
                                                                                        ⟦ M ⟧ᶜ (⟦ ρ ⟧ʳ γ' , a)
                                                                                        ∎)))


-------------------
----- Substitution
-------------------

var-aux-lemma-s : {Γ Γ' : Ctx} {A : Ty} → (γ' : ⟦ Γ' ⟧ᵉ) → (σ : Sub Γ Γ') → (x : A ∈ Γ) → ⟦ σ x ⟧ᵛ γ' `≡ var-aux x (⟦ σ ⟧ˢ γ')
var-aux-lemma-s γ' σ Z = refl
var-aux-lemma-s γ' σ (S x) = var-aux-lemma-s γ' (λ z → σ (S z)) x

⟦exts-sub∘S⟧ˢ-lemma : {Γ Γ' : Ctx} → ∀ {A : Ty} {a : ⟦ A ⟧ᵗ} → (σ : Sub Γ Γ') → (γ : ⟦ Γ' ⟧ᵉ) → ⟦ (exts-sub σ) ∘ S ⟧ˢ (γ , a) `≡ ⟦ σ ⟧ˢ γ
⟦exts-sub∘S⟧ˢ-lemma {Γ = ∅} σ γ = refl
⟦exts-sub∘S⟧ˢ-lemma {Γ = Γ ,, A} {a = a} σ γ = cong₂ (λ f g → f , g) (⟦exts-sub∘S⟧ˢ-lemma (λ z → σ (S z)) γ) aux
    where
        aux : ⟦ ren-v wk-ren (σ Z) ⟧ᵛ (γ , a) `≡ ⟦ σ Z ⟧ᵛ γ
        aux = 
            begin
                ⟦ ren-v wk-ren (σ Z) ⟧ᵛ (γ , a)
                ≡⟨ cong (λ f → f (γ , a)) (lemma-ren-v wk-ren (σ Z)) ⟩
                ⟦ σ Z ⟧ᵛ (⟦ wk-ren ⟧ʳ (γ , a))
                ≡⟨ cong (λ f → ⟦ σ Z ⟧ᵛ f) ⟦S⟧ʳ-lema ⟩
                ⟦ σ Z ⟧ᵛ γ
                ∎
              
⟦var⟧ˢ≡id-lemma : {Γ : Ctx} → (γ : ⟦ Γ ⟧ᵉ) → ⟦ var ⟧ˢ γ `≡ γ
⟦var⟧ˢ≡id-lemma {Γ = ∅} γ = refl
⟦var⟧ˢ≡id-lemma {Γ = Γ ,, x} γ = 
    begin
        (⟦ var ∘ S ⟧ˢ γ , proj₂ γ)
        ≡⟨ cong (λ f → (f , proj₂ γ)) (⟦exts-sub∘S⟧ˢ-lemma var (proj₁ γ)) ⟩
        ⟦ var ⟧ˢ (proj₁ γ) , proj₂ γ
        ≡⟨ cong (λ f → (f , proj₂ γ)) (⟦var⟧ˢ≡id-lemma (proj₁ γ)) ⟩
        γ
        ∎

lemma-⟦exts-sub⟧ˢ : {Γ Γ' : Ctx} → (σ : Sub Γ Γ') → (γ : ⟦ Γ' ⟧ᵉ) → ∀ {A : Ty} {a : ⟦ A ⟧ᵗ} → ⟦ exts-sub σ ⟧ˢ (γ , a) `≡  (⟦ σ ⟧ˢ γ , a)
lemma-⟦exts-sub⟧ˢ {Γ = ∅} σ γ = refl
lemma-⟦exts-sub⟧ˢ {Γ = Γ ,, x} {Γ' = Γ'} σ γ {a = a} = cong₂ (λ f g → ((f , g) , a)) (⟦exts-sub∘S⟧ˢ-lemma (λ z → σ (S z)) γ) (aux-1 (σ Z))
    where
        aux-1 : {A : Ty} → (V : Γ' ⊢ᵛ A) → ⟦ ren-v wk-ren V ⟧ᵛ (γ , a) `≡ ⟦ V ⟧ᵛ γ
        aux-1 V = 
            begin
                ⟦ ren-v wk-ren (V) ⟧ᵛ (γ , a) 
                ≡⟨ cong (λ f → f (γ , a)) (lemma-ren-v wk-ren (V)) ⟩
                ⟦ V ⟧ᵛ (⟦ wk-ren ⟧ʳ (γ , a))
                ≡⟨ cong (λ f → ⟦ V ⟧ᵛ f) ⟦S⟧ʳ-lema ⟩
                ⟦ V ⟧ᵛ γ
                ∎


mutual
    lemma-sub-c : {A : Ty} {Γ Γ' : Ctx} → (σ : Sub Γ Γ') → (M : Γ ⊢ᶜ A) → ⟦ sub-c σ M ⟧ᶜ `≡ (⟦ M ⟧ᶜ ∘ ⟦ σ ⟧ˢ)

    lemma-sub-c σ (return V) = fun-ext (λ γ → fun-ext λ s → cong (λ f → inj₂ ( f γ , s)) (lemma-sub-v σ V))    
    lemma-sub-c {Γ' = Γ'} σ (`let M `in N) = fun-ext (λ γ → fun-ext (λ s → lemma-sub-let-in-aux s γ))
        where
            lemma-sub-let-in-aux : (s : State) → (γ : ⟦ Γ' ⟧ᵉ) → ⟦ sub-c σ (`let M `in N) ⟧ᶜ γ s `≡ (⟦ `let M `in N ⟧ᶜ ∘ ⟦ σ ⟧ˢ) γ s
            lemma-sub-let-in-aux s γ rewrite lemma-sub-c σ M with (⟦ M ⟧ᶜ (⟦ σ ⟧ˢ γ) s)
            ... | inj₁ e = refl
            ... | inj₂ v = 
                begin
                    ⟦ sub-c (exts-sub σ) N ⟧ᶜ (γ , proj₁ v) (proj₂ v)
                    ≡⟨ cong (λ f → f (γ , proj₁ v) (proj₂ v)) (lemma-sub-c ((exts-sub σ)) N) ⟩
                    ⟦ N ⟧ᶜ (⟦ exts-sub σ ⟧ˢ (γ , proj₁ v)) (proj₂ v)
                    ≡⟨ cong (λ f → ⟦ N ⟧ᶜ f (proj₂ v)) (lemma-⟦exts-sub⟧ˢ σ γ) ⟩
                    ⟦ N ⟧ᶜ (⟦ σ ⟧ˢ γ , proj₁ v) (proj₂ v)
                    ∎
    lemma-sub-c σ (app V W) = fun-ext (λ γ → cong₂ (λ f g → (f γ) (g γ)) (lemma-sub-v σ V) (lemma-sub-v σ W))
    lemma-sub-c σ (`raise e) = refl
    lemma-sub-c {Γ' = Γ'} σ (`get M) = fun-ext (λ γ → fun-ext (λ s → lemma-sub-get-aux γ s))
        where
            lemma-sub-get-aux : (γ : ⟦ Γ' ⟧ᵉ) (s : State) → ⟦ sub-c (exts-sub σ) M ⟧ᶜ (γ , s) s `≡ ⟦ M ⟧ᶜ (⟦ σ ⟧ˢ γ , s) s
            lemma-sub-get-aux γ s = 
                begin
                    ⟦ sub-c (exts-sub σ) M ⟧ᶜ (γ , s) s
                    ≡⟨ cong (λ f → f (γ , s) s) (lemma-sub-c (exts-sub σ) M) ⟩
                    (⟦ M ⟧ᶜ (⟦ exts-sub σ ⟧ˢ (γ , s))) s
                    ≡⟨ cong (λ f → (⟦ M ⟧ᶜ f) s) (lemma-⟦exts-sub⟧ˢ σ γ) ⟩
                    ⟦ M ⟧ᶜ (⟦ σ ⟧ˢ γ , s) s
                    ∎
    lemma-sub-c σ (`put V M) = fun-ext (λ γ → fun-ext (λ s → cong₂ (λ f g → (f γ) (g γ)) (lemma-sub-c σ M) (lemma-sub-v σ V)))


    lemma-sub-v : {A : Ty} {Γ Γ' : Ctx} → (σ : Sub Γ Γ') → (V : Γ ⊢ᵛ A) → ⟦ sub-v σ V ⟧ᵛ `≡ (⟦ V ⟧ᵛ ∘ ⟦ σ ⟧ˢ)
    lemma-sub-v σ (var x) = fun-ext (λ γ' → var-aux-lemma-s γ' σ x)
    lemma-sub-v σ (const x) = refl
    lemma-sub-v σ ⋆ = refl
    lemma-sub-v {A = A} {Γ = Γ} {Γ' = Γ'} σ (`λ M) = fun-ext (λ γ → fun-ext (λ a → (begin
                                                                                        ⟦ sub-c (exts-sub σ) M ⟧ᶜ (γ , a)
                                                                                        ≡⟨ cong (λ f → f (γ , a)) (lemma-sub-c (exts-sub σ) M) ⟩
                                                                                        ⟦ M ⟧ᶜ (⟦ exts-sub σ ⟧ˢ (γ , a))
                                                                                        ≡⟨ cong (λ f → ⟦ M ⟧ᶜ f) (lemma-⟦exts-sub⟧ˢ σ γ) ⟩
                                                                                        ⟦ M ⟧ᶜ (⟦ σ ⟧ˢ γ , a)
                                                                                        ∎)))



     
-----------------------------------------------------------------
-------------------------- SOUNDNESS ----------------------------
-----------------------------------------------------------------

mutual
    soundness-c : {A : Ty} {Γ : Ctx} {M N : Γ ⊢ᶜ A} → Γ ⊢ᶜ M ≡ N → ⟦ M ⟧ᶜ `≡ ⟦ N ⟧ᶜ

    soundness-c ≡-refl = refl
    soundness-c (≡-symm p) = sym (soundness-c p)
    soundness-c (≡-trans {M = M} {N = N} {O = O} p q) = 
        begin
            ⟦ M ⟧ᶜ
            ≡⟨ soundness-c p ⟩
            ⟦ N ⟧ᶜ
            ≡⟨ soundness-c q ⟩
            ⟦ O ⟧ᶜ
            ∎

    soundness-c (cong-app p q) = fun-ext (λ γ → cong₂ (λ f g → (f γ) (g γ)) (soundness-v p) (soundness-v q))
    
    soundness-c {Γ = Γ} (cong-letin {M = M} {M' = M'} {N = N} {N' = N'} p q) = fun-ext (λ γ → fun-ext (λ s → soundness-c-cong-letin-aux γ s))
        where
            soundness-c-cong-letin-aux : (γ : ⟦ Γ ⟧ᵉ) → (s : State) →  ⟦ `let M `in N ⟧ᶜ γ s `≡ ⟦ `let M' `in N' ⟧ᶜ γ s
            soundness-c-cong-letin-aux γ s rewrite soundness-c p with ⟦ M' ⟧ᶜ γ s
            ... | inj₁ e = refl
            ... | inj₂ v = cong (λ f → f (γ , proj₁ v) (proj₂ v)) (soundness-c q)
    
    soundness-c (cong-return p) = cong (λ f → (λ γ s → inj₂ (f γ , s))) (soundness-v p)


    soundness-c {Γ = Γ} (β-`λ {M = M} {V = V}) = fun-ext soundness-β-`λ-aux
        where
            soundness-β-`λ-aux : (γ : ⟦ Γ ⟧ᵉ) → ⟦ M ⟧ᶜ (γ , ⟦ V ⟧ᵛ γ) `≡ ⟦ sub-c (ext-sub var V) M ⟧ᶜ γ
            soundness-β-`λ-aux γ = sym (
                begin
                    ⟦ sub-c (ext-sub var V) M ⟧ᶜ γ
                    ≡⟨ cong (λ f → f γ) (lemma-sub-c (ext-sub var V) M) ⟩
                    ⟦ M ⟧ᶜ (⟦ var ⟧ˢ γ , ⟦ V ⟧ᵛ γ)
                    ≡⟨ cong (λ f →  ⟦ M ⟧ᶜ (f , ⟦ V ⟧ᵛ γ)) (⟦var⟧ˢ≡id-lemma γ) ⟩
                    ⟦ M ⟧ᶜ (γ , ⟦ V ⟧ᵛ γ)
                    ∎ )
    
    soundness-c (β-letin {V = V} {M = M}) = fun-ext (λ γ → fun-ext (λ s → sym (
        begin
            ⟦ sub-c (ext-sub var V) M ⟧ᶜ γ s 
            ≡⟨ cong (λ f → f γ s) (lemma-sub-c (ext-sub var V) M) ⟩
            ⟦ M ⟧ᶜ (⟦ ext-sub var V ⟧ˢ γ) s
            ≡⟨ cong (λ f → ⟦ M ⟧ᶜ (f , ⟦ V ⟧ᵛ γ) s) (⟦var⟧ˢ≡id-lemma γ) ⟩
            ⟦ M ⟧ᶜ (γ , ⟦ V ⟧ᵛ γ) s
            ∎
        )))

    soundness-c {Γ = Γ} (η-letin {M = M}) = fun-ext (λ γ → fun-ext (λ s → soundness-c-η-letin-aux γ s))
        where
            soundness-c-η-letin-aux : (γ : ⟦ Γ ⟧ᵉ) → (s : State) → ⟦ M ⟧ᶜ γ s `≡ ⟦ `let M `in return (var Z) ⟧ᶜ γ s
            soundness-c-η-letin-aux γ s with ⟦ M ⟧ᶜ γ s
            ... | inj₁ e = refl
            ... | inj₂ v = refl
            
    soundness-c {A = A} {Γ = Γ} (let-assoc {A = B} {B = C} {M = M} {N = N} {O = O}) = fun-ext (λ γ → fun-ext (λ s → let-assoc-aux γ s))
        where
            let-assoc-aux : (γ : ⟦ Γ ⟧ᵉ) → (s : State) →  letin-aux (`let M `in N) O γ s `≡ letin-aux M (`let N `in ren-c (exts-ren S) O) γ s
            let-assoc-aux γ s with (⟦ M ⟧ᶜ γ s)
            ... | inj₁ e = refl
            ... | inj₂ v with (⟦ N ⟧ᶜ (γ , proj₁ v) (proj₂ v))
            ...             | inj₁ e' = refl
            ...             | inj₂ v' = sym (begin
                                                ⟦ ren-c (exts-ren S) O ⟧ᶜ ((γ , proj₁ v) , proj₁ v') (proj₂ v')
                                                ≡⟨ cong (λ f → f ((γ , proj₁ v) , proj₁ v') (proj₂ v')) (lemma-ren-c (exts-ren S) O) ⟩
                                                (⟦ O ⟧ᶜ (⟦ exts-ren S ⟧ʳ ((γ , proj₁ v) , proj₁ v'))) (proj₂ v')
                                                ≡⟨ cong (λ f →  (⟦ O ⟧ᶜ (f , proj₁ v') ) (proj₂ v')) (⟦S∘ρ⟧ʳ-lemma S ((γ , proj₁ v))) ⟩
                                                (⟦ O ⟧ᶜ ( ⟦ S ⟧ʳ (γ , proj₁ v) , proj₁ v') ) (proj₂ v')
                                                ≡⟨ cong (λ f → (⟦ O ⟧ᶜ (f , proj₁ v') ) (proj₂ v')) ⟦S⟧ʳ-lema ⟩
                                                (⟦ O ⟧ᶜ (γ , proj₁ v') ) (proj₂ v')
                                                ≡⟨ refl ⟩
                                                ⟦ O ⟧ᶜ (γ , proj₁ v') (proj₂ v')
                                                ∎)
        
    soundness-c (let-put {V = V} {M = M} {N = N}) = refl
    soundness-c {A = A} {Γ = Γ} (let-get {A = B} {M = M} {N = N}) = fun-ext (λ γ → fun-ext (λ s → let-get-aux γ s))
        where
            let-get-aux : (γ : ⟦ Γ ⟧ᵉ) → (s : State) → ⟦ `let `get M `in N ⟧ᶜ γ s `≡ ⟦ `get (`let M `in ren-c (exts-ren wk-ren) N) ⟧ᶜ γ s
            let-get-aux γ s with (⟦ M ⟧ᶜ (γ , s) s)
            ... | inj₁ e = refl
            ... | inj₂ v = sym (begin
                                    ⟦ ren-c (exts-ren S) N ⟧ᶜ ((γ , s) , proj₁ v) (proj₂ v)
                                    ≡⟨ cong (λ f → f ((γ , s) , proj₁ v) (proj₂ v)) (lemma-ren-c (exts-ren S) N) ⟩
                                    (⟦ N ⟧ᶜ ((⟦ exts-ren S ⟧ʳ) ((γ , s) , proj₁ v))) (proj₂ v)
                                    ≡⟨ cong (λ f → ⟦ N ⟧ᶜ (f , proj₁ v) (proj₂ v)) (⟦S∘ρ⟧ʳ-lemma S (γ , s)) ⟩
                                    ⟦ N ⟧ᶜ (⟦ S ⟧ʳ (γ , s) , proj₁ v) (proj₂ v)
                                    ≡⟨ cong (λ f → ⟦ N ⟧ᶜ (f , proj₁ v) (proj₂ v)) ⟦S⟧ʳ-lema ⟩
                                    ⟦ N ⟧ᶜ (γ , proj₁ v) (proj₂ v)
                                    ∎)
                                    
    soundness-c {Γ = Γ} (put-get {V = V} {M = M}) = fun-ext (λ γ → fun-ext (λ _ → cong (λ f → f (⟦ V ⟧ᵛ γ)) (soundness-put-get-aux γ)))
        where
            soundness-put-get-aux : (γ : ⟦ Γ ⟧ᵉ) → ⟦ M ⟧ᶜ (γ , ⟦ V ⟧ᵛ γ) `≡ ⟦ sub-c (ext-sub var V) M ⟧ᶜ γ
            soundness-put-get-aux γ = sym ( 
                begin
                    ⟦ sub-c (ext-sub var V) M ⟧ᶜ γ
                    ≡⟨ cong (λ f → f γ) (lemma-sub-c (ext-sub var V) M) ⟩
                    ⟦ M ⟧ᶜ ( ⟦ ext-sub var V ⟧ˢ γ )
                    ≡⟨ cong (λ f → ⟦ M ⟧ᶜ (f , ⟦ V ⟧ᵛ γ)) (⟦var⟧ˢ≡id-lemma γ) ⟩
                    ⟦ M ⟧ᶜ (γ , ⟦ V ⟧ᵛ γ)
                    ∎) 

    soundness-c (η-get {M = M})  = fun-ext (λ γ → fun-ext (λ s → cong (λ f → f s) (begin
                                                                                ⟦ ren-c S M ⟧ᶜ (γ , s)
                                                                                ≡⟨ cong (λ f → f (γ , s)) (lemma-ren-c S M) ⟩
                                                                                (⟦ M ⟧ᶜ ∘ ⟦ S ⟧ʳ) (γ , s)
                                                                                ≡⟨ cong (λ f → ⟦ M ⟧ᶜ f) ⟦S⟧ʳ-lema ⟩
                                                                                ⟦ M ⟧ᶜ γ
                                                                                ∎)))


    soundness-c put-put = refl
    soundness-c raise-put = refl
    soundness-c raise-get = refl
    soundness-c raise-let = refl



    soundness-v : {A : Ty} {Γ : Ctx} {V W : Γ ⊢ᵛ A} → Γ ⊢ᵛ V ≡ W → ⟦ V ⟧ᵛ `≡ ⟦ W ⟧ᵛ

    soundness-v ≡-refl = refl
    soundness-v (≡-symm p) = sym (soundness-v p)
    soundness-v (≡-trans {V = V} {W = W} {U = U} p q) = 
        begin
            ⟦ V ⟧ᵛ
            ≡⟨ soundness-v p ⟩
            ⟦ W ⟧ᵛ
            ≡⟨ soundness-v q ⟩
            ⟦ U ⟧ᵛ
            ∎
            
    soundness-v (cong-`λ p) = fun-ext (λ γ → fun-ext (λ a → cong (λ f → f (γ , a)) (soundness-c p)))


    soundness-v η-⋆ = fun-ext (λ γ → refl)

    soundness-v {Γ = Γ} (η-`λ {A = A} {V = V}) = fun-ext (λ γ → fun-ext (λ a → cong (λ f → f a) (soundness-v-η-reduction-aux γ a)))
        where
            soundness-v-η-reduction-aux : (γ : ⟦ Γ ⟧ᵉ) → (a : ⟦ A ⟧ᵗ) → ⟦ V ⟧ᵛ γ `≡ ⟦ sub-v wk-sub V ⟧ᵛ (γ , a)
            soundness-v-η-reduction-aux γ a = sym (
                begin
                    ⟦ sub-v wk-sub V ⟧ᵛ (γ , a)
                    ≡⟨ cong (λ f → f (γ , a)) (lemma-sub-v wk-sub V) ⟩
                    ⟦ V ⟧ᵛ (⟦ var ∘ S ⟧ˢ (γ , a))
                    ≡⟨ cong (λ f → ⟦ V ⟧ᵛ f) (⟦exts-sub∘S⟧ˢ-lemma var γ) ⟩
                    ⟦ V ⟧ᵛ (⟦ var ⟧ˢ γ)
                    ≡⟨ cong (λ f → ⟦ V ⟧ᵛ f) (⟦var⟧ˢ≡id-lemma γ) ⟩
                    ⟦ V ⟧ᵛ γ
                    ∎
                )
                