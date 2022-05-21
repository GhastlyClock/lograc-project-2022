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


-- ⟦ (λ x → exts-ren ρ (S x)) ⟧ʳ (γ , proj₁ v) `≡ ⟦ ρ ⟧ʳ γ
-- (⟦ exts-ren ρ ⟧ʳ (γ' , a)) `≡ (⟦ ρ ⟧ᵉ γ')
lemma-za-r : {Γ Γ' : Ctx} → (ρ : Ren Γ Γ') → (γ' : ⟦ Γ' ⟧ᵉ) → ∀ {A : Ty} {a : ⟦ A ⟧ᵗ} → ⟦ (λ x → S (ρ x)) ⟧ʳ (γ' , a) `≡ ⟦ ρ ⟧ʳ γ'
lemma-za-r {Γ = ∅} ρ γ' = refl
lemma-za-r {Γ = Γ ,, x} ρ γ' = cong (λ f → ( f , var-aux (ρ Z) γ' )) (lemma-za-r (λ z → ρ (S z)) γ')


var-aux-lemma : {A : Ty} {Γ Γ' : Ctx} → (ρ : Ren Γ Γ') → (x : A ∈ Γ) → (γ' : ⟦ Γ' ⟧ᵉ) → var-aux (ρ x) γ' `≡ var-aux x (⟦ ρ ⟧ʳ γ')
var-aux-lemma ρ Z γ' = refl
var-aux-lemma ρ (S x) γ' = var-aux-lemma (λ z → ρ (S z)) x γ'

mutual
    lemma-ren-c : {A : Ty} {Γ Γ' : Ctx} → (ρ : Ren Γ Γ') → (M : Γ ⊢ᶜ A) → ⟦ ren-c ρ M ⟧ᶜ `≡ (⟦ M ⟧ᶜ ∘ ⟦ ρ ⟧ʳ)
    
    lemma-ren-c {A = A} {Γ = Γ} {Γ' = Γ'} ρ (return V) = fun-ext (λ γ → fun-ext (λ s → cong (λ x → inj₂ ( x , s )) (lemma-ren-c-return-aux γ V)))
        where
            lemma-ren-c-return-aux : (γ' : ⟦ Γ' ⟧ᵉ) → (V : Γ ⊢ᵛ A) →  ⟦ ren-v ρ V ⟧ᵛ γ' `≡ ⟦ V ⟧ᵛ (⟦ ρ ⟧ʳ γ')
            lemma-ren-c-return-aux γ' (var x) = var-aux-lemma ρ x γ'
            lemma-ren-c-return-aux γ' (const x) = refl
            lemma-ren-c-return-aux γ' ⋆ = refl
            lemma-ren-c-return-aux γ' `true = refl
            lemma-ren-c-return-aux γ' `false = refl
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
                            ≡⟨ cong (λ f → ⟦ M ⟧ᶜ (f , proj₁ v)) (lemma-za-r ρ γ) ⟩
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
                    ≡⟨ cong (λ f → ⟦ M ⟧ᶜ (f , s)) (lemma-za-r ρ γ) ⟩
                    ⟦ M ⟧ᶜ (⟦ ρ ⟧ʳ γ , s)
                    ∎

    lemma-ren-c ρ (`put s M) = fun-ext (λ γ → fun-ext (λ _ → cong₂ (λ f g → (f γ) (g γ)) (lemma-ren-c ρ M) (lemma-ren-v ρ s)))


    lemma-ren-v : {A : Ty} {Γ Γ' : Ctx} → (ρ : Ren Γ Γ') → (V : Γ ⊢ᵛ A) → ⟦ ren-v ρ V ⟧ᵛ `≡ (⟦ V ⟧ᵛ ∘ ⟦ ρ ⟧ʳ)
    lemma-ren-v ρ (var x) = fun-ext λ γ → var-aux-lemma ρ x γ
    lemma-ren-v ρ (const x) = refl
    lemma-ren-v ρ ⋆ = refl
    lemma-ren-v ρ `true = refl
    lemma-ren-v ρ `false = refl
    lemma-ren-v {A = A} {Γ = Γ} {Γ' = Γ'} ρ (`λ M) = fun-ext (λ γ' → fun-ext (λ a → (begin
                                                                                        ⟦ ren-c (exts-ren ρ) M ⟧ᶜ (γ' , a)
                                                                                        ≡⟨ cong (λ f → f (γ' , a)) (lemma-ren-c (exts-ren ρ) M) ⟩
                                                                                        (⟦ M ⟧ᶜ ∘ ⟦ exts-ren ρ ⟧ʳ) (γ' , a)
                                                                                        ≡⟨ cong (λ f → ⟦ M ⟧ᶜ (f , a)) (lemma-za-r ρ γ') ⟩
                                                                                        ⟦ M ⟧ᶜ (⟦ ρ ⟧ʳ γ' , a)
                                                                                        ∎)))




                                                                                        


soundness : {A : Ty} {Γ : Ctx} {M N : Γ ⊢ᶜ A} → Γ ⊢ᶜ M ≡ N → ⟦ M ⟧ᶜ `≡ ⟦ N ⟧ᶜ

-- ⟦ app (`λ M₁) V ⟧ᶜ `≡ ⟦ M₁ [ V ] ⟧ᶜ
-- (λ γ → ⟦ M₁ ⟧ᶜ (γ , ⟦ V ⟧ᵛ γ)) `≡ ⟦ M₁ [ V ] ⟧ᶜ
-- ⟦ app (`λ M) V ⟧ᶜ `≡ ⟦ M [ V ] ⟧ᶜ

-- ⟦ app (`λ M₁) V₁ ⟧ᶜ `≡ ⟦ M₁ [ V₁ ] ⟧ᶜ
soundness {A = A} {Γ = Γ} β-reduction = {!   !}
    -- where
    --     β-reduction-aux : {!   !} 
    --     β-reduction-aux = {!   !}
    -- ⟦ app (`λ M) V ⟧ᶜ `≡ ⟦ M [ V ] ⟧ᶜ
        -- β-reduction-aux : {B : Ty} {V : Γ ⊢ᵛ B} {M : Γ ,, B ⊢ᶜ A } → ⟦ app (`λ M) V ⟧ᶜ `≡ ⟦ _[_] M V ⟧ᶜ
        -- β-reduction-aux = {!   !}


soundness let-put = refl
soundness let-get = {!   !}


-- ⟦ `put V (`get M) ⟧ᶜ `≡ ⟦ `put V (M [ V ]) ⟧ᶜ

-- put (⟦ V ⟧ᵛ γ) (get (λ s → ⟦ M ⟧ᶜ (γ , s))) `≡
--       put (⟦ V ⟧ᵛ γ) (⟦ M [ V ] ⟧ᶜ γ)
soundness {A = A} {Γ = Γ} put-get = fun-ext (λ γ → {!   !})
    where
        put-get-aux : {M : Γ ,, TState ⊢ᶜ A} {V : Γ ⊢ᵛ TState} → (γ : ⟦ Γ ⟧ᵉ) → (get (λ s → ⟦ M ⟧ᶜ (γ , s))) `≡  (⟦ _[_] M V ⟧ᶜ γ)
        put-get-aux {M = M} {V = V} γ = fun-ext λ s → aux s
            where
                aux : (s : State) → ⟦ M ⟧ᶜ (γ , s) s `≡ ⟦ sub-c (σ-aux V) M ⟧ᶜ γ s
                aux s with ⟦ M ⟧ᶜ (γ , s) s
                ... | inj₁ e = {!  !}
                ... | inj₂ v = {!   !}


-- ⟦ `get (ren-c S N) ⟧ᶜ `≡ ⟦ N ⟧ᶜ
-- (λ γ → get (λ s → ⟦ ren-c S N ⟧ᶜ (γ , s))) `≡ ⟦ N ⟧ᶜ


-- ⟦ ren-c ρ N ⟧ᶜ `≡ (⟦ N ⟧ᶜ ∘ ⟦ ρ ⟧ʳ)
-- (λ γ s → ⟦ ren-c S N ⟧ᶜ (γ , s) s) `≡ ⟦ N ⟧ᶜ
soundness {A = A} {Γ = Γ} {M = M} {N = N} GET = fun-ext λ γ → {!   !}
    -- begin
    --     ⟦ `get (ren-c S N) ⟧ᶜ
    --     -- ≡⟨ lemma-ren-c ⟩
    --     ≡⟨ lemma-ren-c {! N !} ⟩
    --     {!   !}


soundness put-put = refl
soundness raise-put = refl
soundness raise-get = refl
soundness raise-let = refl

-- ⟦ M ⟧ᶜ (γ , ⟦ V ⟧ᵛ γ) s `≡ ⟦ sub-c (σ-aux V) M ⟧ᶜ γ s
soundness return-left = {!   !}
    -- where
    --     return-left-aux : {A B : Ty} {Γ : Ctx} {V : Γ ⊢ᵛ B} {M : Γ ,, B ⊢ᶜ A} → (γ : ⟦ Γ ⟧ᵉ) → (s : State) →  letin-aux (return V) M γ s `≡ ⟦ _[_] M V ⟧ᶜ γ s
    --     return-left-aux γ s = {!   !}
    -- where
    --     return-left-aux : {B : Ty} {V : Γ ⊢ᵛ B} {M : Γ ,, B ⊢ᶜ A} → (γ : ⟦ Γ ⟧ᵉ) → (s : State) →  ⟦ `let return V `in M ⟧ᶜ γ s `≡ ⟦ _[_] M V ⟧ᶜ γ s
    --     return-left-aux = {!   !}
    --     return-left-aux : {B : Ty} {V : Γ ⊢ᵛ B} {M : Γ ,, B ⊢ᶜ A} → (γ : ⟦ Γ ⟧ᵉ) → (s : State) → ((((letin-aux (return V)) M) γ) s) `≡ (((⟦ (_[_] M V) ⟧ᶜ) γ) s)
    --     return-left-aux = {!   !}


soundness {Γ = Γ} {N = N} return-right = fun-ext (λ γ → fun-ext (λ s → return-right-aux γ s))
    where
        return-right-aux : (γ : ⟦ Γ ⟧ᵉ) → (s : State) → letin-aux N (return (var Z)) γ s `≡ ⟦ N ⟧ᶜ γ s
        return-right-aux γ s with ⟦ N ⟧ᶜ γ s
        ... | inj₁ e = refl
        ... | inj₂ v = refl


    --     return-right-aux : (γ : ⟦ Γ ⟧ᵉ) → letin-aux N (return (var Z)) γ `≡ ⟦ N ⟧ᶜ γ
    --     return-right-aux γ = {!   !}
-- letin-aux (`let M `in N) O γ `≡ letin-aux M (`let N `in ren-c (exts-ren S) O) γ
-- soundness let-assoc = fun-ext λ γ → fun-ext (λ s → {!   !})
-- ⟦ `let `let M `in N `in O ⟧ᶜ `≡ ⟦ `let M `in (`let N `in ren-c (exts-ren S) O) ⟧ᶜ
----------------------------

-- (letin-aux (`let M `in N) O γ s
--        | (letin-aux M N γ s | ⟦ M ⟧ᶜ γ s))
--       `≡ (letin-aux M (`let N `in ren-c (exts-ren S) O) γ s | ⟦ M ⟧ᶜ γ s)

-- letin-aux (`let M `in N) O γ s `≡
--       letin-aux M (`let N `in ren-c (exts-ren S) O) γ s

soundness {A = A} {Γ = Γ} let-assoc = fun-ext (λ γ → fun-ext (λ s → {!   !}))
    where
        aux : {!   !} 
        aux = {!   !}

        let-assoc-aux : ∀ {B C : Ty} {O : Γ ,, B ⊢ᶜ A} {N : Γ ,, C ⊢ᶜ B} {M : Γ ⊢ᶜ C} → (γ : ⟦ Γ ⟧ᵉ) → (s : State) → letin-aux (`let M `in N) O γ s `≡ letin-aux M (`let N `in ren-c (exts-ren S) O) γ s
        let-assoc-aux {N = N} {M = M} γ s with (letin-aux M N γ s) | (⟦ M ⟧ᶜ γ s)
        ... | inj₁ x | inj₁ x₁ = refl
        ... | inj₁ x | inj₂ y = {!   !}
        ... | inj₂ y | inj₁ x = refl
        ... | inj₂ y | inj₂ y₁ = {!   !}     