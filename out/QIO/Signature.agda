{-
This second-order signature was created from the following second-order syntax description:

syntax QIO

type
  T : 0-ary
  P : 0-ary

term
  new      : P.T  ->  T
  measure  : P  T  T  ->  T
  applyX   : P  P.T  ->  T
  applyI2  : P  P.T  ->  T
  applyDuv : P  P  (P,P).T  ->  T
  applyDu  : P  P.T  ->  T
  applyDv  : P  P.T  ->  T

theory
  (A) a:P   t u:T         |> applyX (a, b.measure(b, t, u)) = measure(a, u, t)
  (B) a:P   b:P  t u:P.T  |> measure(a, applyDu(b, b.t[b]), applyDv(b, b.u[b])) = applyDuv(a, b, a b.measure(a, t[b], u[b]))
  (D) t u:T               |> new(a.measure(a, t, u)) = t
  (E) b:P  t:(P, P).T     |> new(a.applyDuv(a, b, a b. t[a,b])) = applyDu(b, b.new(a.t[a,b]))
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
  newₒ measureₒ applyXₒ applyI2ₒ applyDuvₒ applyDuₒ applyDvₒ : QIOₒ

-- Term signature
QIO:Sig : Signature QIOₒ
QIO:Sig = sig λ
  {  newₒ       → (P ⊢₁ T) ⟼₁ T
  ;  measureₒ   → (⊢₀ P) , (⊢₀ T) , (⊢₀ T) ⟼₃ T
  ;  applyXₒ    → (⊢₀ P) , (P ⊢₁ T) ⟼₂ T
  ;  applyI2ₒ   → (⊢₀ P) , (P ⊢₁ T) ⟼₂ T
  ;  applyDuvₒ  → (⊢₀ P) , (⊢₀ P) , (P , P ⊢₂ T) ⟼₃ T
  ;  applyDuₒ   → (⊢₀ P) , (P ⊢₁ T) ⟼₂ T
  ;  applyDvₒ   → (⊢₀ P) , (P ⊢₁ T) ⟼₂ T
  }

open Signature QIO:Sig public
