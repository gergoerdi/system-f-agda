module SystemF where

open import SimplyTyped.Ctx as Ctx hiding (Ctx; Var)
import SimplyTyped.Sub.Core
import SimplyTyped.Ren
import SimplyTyped.Code
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.List hiding (drop)
open import Data.Vec hiding (drop)
open import Data.List.All

module Ren {A : Set} where
  open SimplyTyped.Ren A public
open Ren

data Kind : Set where
  ∗ : Kind

Ctxₜ : Set
Ctxₜ = Ctx.Ctx Kind

Varₜ : Kind → Ctxₜ → Set
Varₜ = Ctx.Var _

module _ where
  open SimplyTyped.Code Kind

  data `Ty₀ : Set where
    `base `fun `forall : `Ty₀

  `Ty : Code
  `Ty = sg `Ty₀ λ
    { `base → node 0 [] λ { [] [] κ → κ ≡ ∗ }
    ; `fun → node 0 ([] ∷ [] ∷ []) λ { [] (κ₁ ∷ κ₂ ∷ []) κ₀ → κ₁ ≡ ∗ × κ₂ ≡ ∗ × κ₀ ≡ ∗ }
    ; `forall → sg Kind λ κ → node 1 ((bound ∷ []) ∷ []) λ { (κ₁ ∷ []) (κ₂ ∷ []) κ₀ → κ₁ ≡ κ × κ₂ ≡ ∗ × κ₀ ≡ ∗ }
    }

  open import SimplyTyped.Typed `Ty renaming (Tm to Ty) public
  open import SimplyTyped.Sub `Ty using ({-_,_-}) renaming (ren to renₜ; sub to subₜ; reflₛ to reflₛₜ) public

  -- base : ∀ {Δ} → Ty Δ ∗
  pattern base = con (sg `base (node [] [] {{refl}}))

  -- _▷_ : ∀ {Δ} → Ty Δ ∗ → Ty Δ ∗ → Ty Δ ∗
  pattern _▷_ t u = con (sg `fun (node [] (t ∷ u ∷ []) {{refl , refl , refl}}))

  -- tforall : ∀ {Δ} κ → Ty (Δ , κ) ∗ → Ty Δ ∗
  pattern tforall κ t = con (sg `forall (sg κ (node (_ ∷ []) (t ∷ []) {{refl , refl , refl}})))

Ctx : Ctxₜ → Set
Ctx Δ = Ctx.Ctx (Ty Δ ∗)

module _ where
  renₜ-ctx : ∀ {Γ Δ} → Γ ⊇ Δ → Ctx Δ → Ctx Γ
  renₜ-ctx Γ⊇Δ ∅ = ∅
  renₜ-ctx Γ⊇Δ (Θ , t) = renₜ-ctx Γ⊇Δ Θ , renₜ Γ⊇Δ t

Var : ∀ {Δ} → Ty Δ ∗ → Ctx Δ → Set
Var = Ctx.Var _

module _ where
  open import SimplyTyped.Sub `Ty

  infixl 23 _·_
  data Tm {Δ : Ctxₜ} (Γ : Ctx Δ) : Ty Δ ∗ → Set where
    var  : ∀ {t}   (v : Var t Γ)                                → Tm Γ t
    lam  : ∀ t {u} (e : Tm (Γ , t) u)                           → Tm Γ (t ▷ u)
    _·_  : ∀ {u t} (f : Tm Γ (u ▷ t)) (e : Tm Γ u)              → Tm Γ t
    Lam  : ∀ κ {t} (e : Tm {Δ , κ} (renₜ-ctx (drop reflᵣ) Γ) t) → Tm Γ (tforall κ t)
    inst : ∀ {κ u} (e : Tm Γ (tforall κ u)) (t : Ty Δ κ)        → Tm Γ (subₜ (reflₛₜ , t) u)

renₜ-ren : ∀ {Θ Θ′ Γ Δ} → (Θ′⊇Θ : Θ′ ⊇ Θ) → Γ ⊇ Δ → (renₜ-ctx Θ′⊇Θ Γ) ⊇ (renₜ-ctx Θ′⊇Θ Δ)
renₜ-ren Θ′⊇θ done     = done
renₜ-ren Θ′⊇θ (drop σ) = drop (renₜ-ren Θ′⊇θ σ)
renₜ-ren Θ′⊇θ (keep σ) = keep (renₜ-ren Θ′⊇θ σ)

module _ where
  module Sub {Θ : Ctxₜ} where
    open SimplyTyped.Sub.Core (Tm {Θ}) public

  renₜ-var : ∀ {Θ Θ′ Γ t} → (Θ′⊇Θ : Θ′ ⊇ Θ) → Var t Γ → Var (renₜ Θ′⊇Θ t) (renₜ-ctx Θ′⊇Θ Γ)
  renₜ-var Θ′⊇Θ vz = vz
  renₜ-var Θ′⊇Θ (vs v) = vs (renₜ-var Θ′⊇Θ v)

  open import SimplyTyped.Sub.Properties `Ty
  open import SimplyTyped.Ren.Properties Kind

  lem₁ : ∀ {κ Θ Θ′ Γ} → (Θ′⊇Θ : Θ′ ⊇ Θ) → renₜ-ctx (keep {t = κ} Θ′⊇Θ) (renₜ-ctx (drop reflᵣ) Γ) ≡ renₜ-ctx (drop reflᵣ) (renₜ-ctx Θ′⊇Θ Γ)
  lem₁ {Γ = ∅}     Θ′⊇Θ     = refl
  lem₁ {κ} {Γ = Γ , t} Θ′⊇Θ rewrite
    ren-⊇⊇ (keep {t = κ} Θ′⊇Θ) (drop reflᵣ) t |
    ren-⊇⊇ (drop {t = κ} reflᵣ) Θ′⊇Θ t |
    Θ′⊇Θ ⊇⊇-refl | refl-⊇⊇ Θ′⊇Θ
    = cong₂ _,_ (lem₁ Θ′⊇Θ) refl

  module _ where
    open import SimplyTyped.Sub `Ty

    lem₂ : ∀ {κ κ′ Θ Θ′} (Θ′⊇Θ : Θ′ ⊇ Θ) (t : Ty Θ κ) (u : Ty (Θ , κ) κ′) →
      renₜ Θ′⊇Θ (subₜ (reflₛₜ , t) u) ≡ subₜ (reflₛₜ , renₜ Θ′⊇Θ t) (renₜ (keep* (κ ∷ []) Θ′⊇Θ) u)
    lem₂ {κ} Θ′⊇Θ t u rewrite
      sym (sub-⊇⊢⋆ Θ′⊇Θ (reflₛₜ , t) u) | Θ′⊇Θ ⊇⊢⋆-refl |
      sym (sub-⊢⋆⊇ (reflₛₜ , renₜ Θ′⊇Θ t) (keep* (κ ∷ []) Θ′⊇Θ) u) |
      refl-⊢⋆⊇ Θ′⊇Θ
      = refl

  renₜ-tm : ∀ {Θ Θ′ Γ t} → (Θ′⊇Θ : Θ′ ⊇ Θ) → Tm Γ t → Tm (renₜ-ctx Θ′⊇Θ Γ) (renₜ Θ′⊇Θ t)
  renₜ-tm Θ′⊇Θ (var v)                         = var (renₜ-var Θ′⊇Θ v)
  renₜ-tm Θ′⊇Θ (lam t e)                       = lam (renₜ Θ′⊇Θ t) (renₜ-tm Θ′⊇Θ e)
  renₜ-tm Θ′⊇Θ (f · e)                         = renₜ-tm Θ′⊇Θ f · renₜ-tm Θ′⊇Θ e
  renₜ-tm {Γ = Γ} Θ′⊇Θ (Lam κ {t} e)           = Lam κ (subst (λ Γ → Tm Γ (renₜ (keep Θ′⊇Θ) t)) (lem₁ Θ′⊇Θ) (renₜ-tm (Ren.keep Θ′⊇Θ) e))
  renₜ-tm {Θ} {Θ′} {Γ} Θ′⊇Θ (inst {κ} {u} e t) rewrite lem₂ Θ′⊇Θ t u
    = inst {u = renₜ (keep* (κ ∷ []) (Θ′⊇Θ)) u} (renₜ-tm Θ′⊇Θ e) (renₜ Θ′⊇Θ t)

  ren : ∀ {Θ Γ Δ t} → Γ ⊇ Δ → Tm {Θ} Δ t → Tm Γ t
  ren Γ⊇Δ (var v)    = var (renᵛ Γ⊇Δ v)
  ren Γ⊇Δ (lam t e)  = lam t (ren (keep Γ⊇Δ) e)
  ren Γ⊇Δ (f · e)    = ren Γ⊇Δ f · ren Γ⊇Δ e
  ren Γ⊇Δ (Lam κ e)  = Lam κ (ren (renₜ-ren (drop (Ren.reflᵣ)) Γ⊇Δ) e)
  ren Γ⊇Δ (inst e t) = inst (ren Γ⊇Δ e) t

  module _ {Ξ : Ctxₜ} where
    open Sub {Ξ}

    infixr 20 _⊇⊢⋆_
    _⊇⊢⋆_ : ∀ {Γ Δ Θ : Ctx Ξ} → Θ ⊇ Γ → Γ ⊢⋆ Δ → Θ ⊢⋆ Δ
    Θ⊇Γ ⊇⊢⋆ ∅       = ∅
    Θ⊇Γ ⊇⊢⋆ (σ , e) = Θ⊇Γ ⊇⊢⋆ σ , ren Θ⊇Γ e

    infixl 20 _⊢⋆⊇_
    _⊢⋆⊇_ : ∀ {Γ Δ Θ} → Γ ⊢⋆ Δ → Δ ⊇ Θ → Γ ⊢⋆ Θ
    σ       ⊢⋆⊇ done       = σ
    (σ , e) ⊢⋆⊇ (drop Δ⊇Θ) = σ ⊢⋆⊇ Δ⊇Θ
    (σ , e) ⊢⋆⊇ (keep Δ⊇Θ) = σ ⊢⋆⊇ Δ⊇Θ , e

    wkₛ : ∀ {t Γ Δ} → Γ ⊢⋆ Δ → Γ , t ⊢⋆ Δ
    wkₛ σ = wk ⊇⊢⋆ σ

    shift : ∀ {t Γ Δ} → Γ ⊢⋆ Δ → Γ , t ⊢⋆ Δ , t
    shift {t} σ = wk ⊇⊢⋆ σ , var vz

  open Sub

  renₜ-sub : ∀ {Θ Θ′ Γ Δ} → (Θ′⊇Θ : Θ′ ⊇ Θ) → Γ ⊢⋆ Δ → (renₜ-ctx Θ′⊇Θ Γ) ⊢⋆ (renₜ-ctx Θ′⊇Θ Δ)
  renₜ-sub Θ′⊇Θ ∅       = ∅
  renₜ-sub Θ′⊇Θ (σ , e) = renₜ-sub Θ′⊇Θ σ , renₜ-tm Θ′⊇Θ e

  sub : ∀ {Θ Γ Δ t} → Γ ⊢⋆ Δ → Tm {Θ} Δ t → Tm Γ t
  sub σ (var v) = subᵛ σ v
  sub σ (lam t e) = lam t (sub (shift σ) e)
  sub σ (f · e) = sub σ f · sub σ e
  sub σ (Lam κ e) = Lam κ (sub (renₜ-sub (drop reflᵣ) σ) e)
  sub σ (inst e t) = inst (sub σ e) t
