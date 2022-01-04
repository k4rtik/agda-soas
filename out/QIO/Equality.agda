{-
This second-order equational theory was created from the following second-order syntax description:

syntax QIO

type
  T : 0-ary
  P : 0-ary

term
  new      : P.T  ->  T
  measure  : P  T1  T2  ->  T
  applyX   : P  P'.T  ->  T
  applyI2  : P  P'.T  ->  T
  applyDuv : P1  P2  (P1,P2).T  ->  T
  applyDu  : P  P'.T  ->  T
  applyDv  : P  P'.T  ->  T

theory
  (A) a:P   t u:T         |> applyX (a, b.measure(b, t, u)) = measure(a, u, t)
  (B) a:P   b:P  t u:P.T  |> measure(a, applyDu(b, b.t[b]), applyDv(b, b.u[b])) = applyDuv(a, b, a b.measure(a, t[b], u[b]))
  (D) t u:T               |> new(a.measure(a, t, u)) = t
  (E) b:P  t:(P1, P2).T   |> new(a.applyDuv(a, b, a b. t[a,b])) = applyDu(b, b.new(a.t[a,b]))
-}

module QIO.Equality where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Families.Build
open import SOAS.ContextMaps.Inductive

open import QIO.Signature
open import QIO.Syntax

open import SOAS.Metatheory.SecondOrder.Metasubstitution QIO:Syn
open import SOAS.Metatheory.SecondOrder.Equality QIO:Syn

private
  variable
    α β γ τ : QIOT
    Γ Δ Π : Ctx

infix 1 _▹_⊢_≋ₐ_

-- Axioms of equality
data _▹_⊢_≋ₐ_ : ∀ 𝔐 Γ {α} → (𝔐 ▷ QIO) α Γ → (𝔐 ▷ QIO) α Γ → Set where
  A : ⁅ P ⁆ ⁅ T ⁆ ⁅ T ⁆̣               ▹ ∅ ⊢                             applyX 𝔞 (measure x₀ 𝔟 𝔠) ≋ₐ measure 𝔞 𝔠 𝔟
  B : ⁅ P ⁆ ⁅ P ⁆ ⁅ P ⊩ T ⁆ ⁅ P ⊩ T ⁆̣ ▹ ∅ ⊢ measure 𝔞 (applyDu 𝔟 (𝔠⟨ x₀ ⟩)) (applyDv 𝔟 (𝔡⟨ x₀ ⟩)) ≋ₐ applyDuv 𝔞 𝔟 (measure x₀ (𝔠⟨ x₁ ⟩) (𝔡⟨ x₁ ⟩))
  D : ⁅ T ⁆ ⁅ T ⁆̣                     ▹ ∅ ⊢                                  new (measure x₀ 𝔞 𝔟) ≋ₐ 𝔞
  E : ⁅ P ⁆ ⁅ P1 · P2 ⊩ T ⁆̣           ▹ ∅ ⊢                    new (applyDuv x₀ 𝔞 (𝔟⟨ x₀ ◂ x₁ ⟩)) ≋ₐ applyDu 𝔞 (new (𝔟⟨ x₀ ◂ x₁ ⟩))

open EqLogic _▹_⊢_≋ₐ_
open ≋-Reasoning


