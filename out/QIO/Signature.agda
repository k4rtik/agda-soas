{-
This second-order signature was created from the following second-order syntax description:

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
  (A) a:P   t u:T |> applyX (a, b.measure(b, t, u)) = measure(a, u, t)
  (B) a:P   b:P  t u:P.T |> measure(a, applyDu(b, b.t[b]), applyDv(b, b.u[b])) = applyDuv(a, b, a b.measure(a, t[b], u[b]))
  (D) t u:T |> new(a.measure(a, t, u)) = t
  (E) b:P  t:(P1, P2).T |> new(a.applyDuv(a, b, a b. t[a,b])) = applyDu(b, b.new(a.t[a,b]))
-}

module QIO.Signature where

open import SOAS.Context

-- Type declaration
data QIOT : Set where
  T : QIOT
  P : QIOT



open import SOAS.Syntax.Signature QIOT public
open import SOAS.Syntax.Build QIOT public

-- Operator symbols
data QIOₒ : Set where
  newₒ : QIOₒ
  measureₒ : {T1 T2 : QIOT} → QIOₒ
  applyXₒ applyI2ₒ applyDuₒ applyDvₒ : {P' : QIOT} → QIOₒ
  applyDuvₒ : {P1 P2 : QIOT} → QIOₒ

-- Term signature
QIO:Sig : Signature QIOₒ
QIO:Sig = sig λ
  {  newₒ                → (P ⊢₁ T) ⟼₁ T
  ; (measureₒ  {T1}{T2}) → (⊢₀ P) , (⊢₀ T1) , (⊢₀ T2) ⟼₃ T
  ; (applyXₒ   {P'})     → (⊢₀ P) , (P' ⊢₁ T) ⟼₂ T
  ; (applyI2ₒ  {P'})     → (⊢₀ P) , (P' ⊢₁ T) ⟼₂ T
  ; (applyDuvₒ {P1}{P2}) → (⊢₀ P1) , (⊢₀ P2) , (P1 , P2 ⊢₂ T) ⟼₃ T
  ; (applyDuₒ  {P'})     → (⊢₀ P) , (P' ⊢₁ T) ⟼₂ T
  ; (applyDvₒ  {P'})     → (⊢₀ P) , (P' ⊢₁ T) ⟼₂ T
  }

open Signature QIO:Sig public
