{-
This second-order term syntax was created from the following second-order syntax description:

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


module QIO.Syntax where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Construction.Structure
open import SOAS.ContextMaps.Inductive

open import SOAS.Metatheory.Syntax

open import QIO.Signature

private
  variable
    Γ Δ Π : Ctx
    P' P1 P2 T1 T2 : QIOT
    𝔛 : Familyₛ

-- Inductive term declaration
module QIO:Terms (𝔛 : Familyₛ) where

  data QIO : Familyₛ where
    var  : ℐ ⇾̣ QIO
    mvar : 𝔛 P' Π → Sub QIO Π Γ → QIO P' Γ

    new      : QIO T (P ∙ Γ) → QIO T Γ
    measure  : QIO P Γ → QIO T1 Γ → QIO T2 Γ → QIO T Γ
    applyX   : QIO P Γ → QIO T (P' ∙ Γ) → QIO T Γ
    applyI2  : QIO P Γ → QIO T (P' ∙ Γ) → QIO T Γ
    applyDuv : QIO P1 Γ → QIO P2 Γ → QIO T (P1 ∙ P2 ∙ Γ) → QIO T Γ
    applyDu  : QIO P Γ → QIO T (P' ∙ Γ) → QIO T Γ
    applyDv  : QIO P Γ → QIO T (P' ∙ Γ) → QIO T Γ

  

  open import SOAS.Metatheory.MetaAlgebra ⅀F 𝔛

  QIOᵃ : MetaAlg QIO
  QIOᵃ = record
    { 𝑎𝑙𝑔 = λ where
      (newₒ      ⋮ a)         → new      a
      (measureₒ  ⋮ a , b , c) → measure  a b c
      (applyXₒ   ⋮ a , b)     → applyX   a b
      (applyI2ₒ  ⋮ a , b)     → applyI2  a b
      (applyDuvₒ ⋮ a , b , c) → applyDuv a b c
      (applyDuₒ  ⋮ a , b)     → applyDu  a b
      (applyDvₒ  ⋮ a , b)     → applyDv  a b
    ; 𝑣𝑎𝑟 = var ; 𝑚𝑣𝑎𝑟 = λ 𝔪 mε → mvar 𝔪 (tabulate mε) }

  module QIOᵃ = MetaAlg QIOᵃ

  module _ {𝒜 : Familyₛ}(𝒜ᵃ : MetaAlg 𝒜) where

    open MetaAlg 𝒜ᵃ

    𝕤𝕖𝕞 : QIO ⇾̣ 𝒜
    𝕊 : Sub QIO Π Γ → Π ~[ 𝒜 ]↝ Γ
    𝕊 (t ◂ σ) new = 𝕤𝕖𝕞 t
    𝕊 (t ◂ σ) (old v) = 𝕊 σ v
    𝕤𝕖𝕞 (mvar 𝔪 mε) = 𝑚𝑣𝑎𝑟 𝔪 (𝕊 mε)
    𝕤𝕖𝕞 (var v) = 𝑣𝑎𝑟 v

    𝕤𝕖𝕞 (new      a)     = 𝑎𝑙𝑔 (newₒ      ⋮ 𝕤𝕖𝕞 a)
    𝕤𝕖𝕞 (measure  a b c) = 𝑎𝑙𝑔 (measureₒ  ⋮ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b , 𝕤𝕖𝕞 c)
    𝕤𝕖𝕞 (applyX   a b)   = 𝑎𝑙𝑔 (applyXₒ   ⋮ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b)
    𝕤𝕖𝕞 (applyI2  a b)   = 𝑎𝑙𝑔 (applyI2ₒ  ⋮ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b)
    𝕤𝕖𝕞 (applyDuv a b c) = 𝑎𝑙𝑔 (applyDuvₒ ⋮ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b , 𝕤𝕖𝕞 c)
    𝕤𝕖𝕞 (applyDu  a b)   = 𝑎𝑙𝑔 (applyDuₒ  ⋮ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b)
    𝕤𝕖𝕞 (applyDv  a b)   = 𝑎𝑙𝑔 (applyDvₒ  ⋮ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b)

    𝕤𝕖𝕞ᵃ⇒ : MetaAlg⇒ QIOᵃ 𝒜ᵃ 𝕤𝕖𝕞
    𝕤𝕖𝕞ᵃ⇒ = record
      { ⟨𝑎𝑙𝑔⟩ = λ{ {t = t} → ⟨𝑎𝑙𝑔⟩ t }
      ; ⟨𝑣𝑎𝑟⟩ = refl
      ; ⟨𝑚𝑣𝑎𝑟⟩ = λ{ {𝔪 = 𝔪}{mε} → cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-tab mε)) }  }
      where
      open ≡-Reasoning
      ⟨𝑎𝑙𝑔⟩ : (t : ⅀ QIO P' Γ) → 𝕤𝕖𝕞 (QIOᵃ.𝑎𝑙𝑔 t) ≡ 𝑎𝑙𝑔 (⅀₁ 𝕤𝕖𝕞 t)
      ⟨𝑎𝑙𝑔⟩ (newₒ      ⋮ _) = refl
      ⟨𝑎𝑙𝑔⟩ (measureₒ  ⋮ _) = refl
      ⟨𝑎𝑙𝑔⟩ (applyXₒ   ⋮ _) = refl
      ⟨𝑎𝑙𝑔⟩ (applyI2ₒ  ⋮ _) = refl
      ⟨𝑎𝑙𝑔⟩ (applyDuvₒ ⋮ _) = refl
      ⟨𝑎𝑙𝑔⟩ (applyDuₒ  ⋮ _) = refl
      ⟨𝑎𝑙𝑔⟩ (applyDvₒ  ⋮ _) = refl

      𝕊-tab : (mε : Π ~[ QIO ]↝ Γ)(v : ℐ α Π) → 𝕊 (tabulate mε) v ≡ 𝕤𝕖𝕞 (mε v)
      𝕊-tab mε new = refl
      𝕊-tab mε (old v) = 𝕊-tab (mε ∘ old) v

    module _ (g : QIO ⇾̣ 𝒜)(gᵃ⇒ : MetaAlg⇒ QIOᵃ 𝒜ᵃ g) where

      open MetaAlg⇒ gᵃ⇒

      𝕤𝕖𝕞! : (t : QIO P' Γ) → 𝕤𝕖𝕞 t ≡ g t
      𝕊-ix : (mε : Sub QIO Π Γ)(v : ℐ P' Π) → 𝕊 mε v ≡ g (index mε v)
      𝕊-ix (x ◂ mε) new = 𝕤𝕖𝕞! x
      𝕊-ix (x ◂ mε) (old v) = 𝕊-ix mε v
      𝕤𝕖𝕞! (mvar 𝔪 mε) rewrite cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-ix mε))
        = trans (sym ⟨𝑚𝑣𝑎𝑟⟩) (cong (g ∘ mvar 𝔪) (tab∘ix≈id mε))
      𝕤𝕖𝕞! (var v) = sym ⟨𝑣𝑎𝑟⟩

      𝕤𝕖𝕞! (new a) rewrite 𝕤𝕖𝕞! a = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (measure a b c) rewrite 𝕤𝕖𝕞! a | 𝕤𝕖𝕞! b | 𝕤𝕖𝕞! c = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (applyX a b) rewrite 𝕤𝕖𝕞! a | 𝕤𝕖𝕞! b = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (applyI2 a b) rewrite 𝕤𝕖𝕞! a | 𝕤𝕖𝕞! b = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (applyDuv a b c) rewrite 𝕤𝕖𝕞! a | 𝕤𝕖𝕞! b | 𝕤𝕖𝕞! c = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (applyDu a b) rewrite 𝕤𝕖𝕞! a | 𝕤𝕖𝕞! b = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (applyDv a b) rewrite 𝕤𝕖𝕞! a | 𝕤𝕖𝕞! b = sym ⟨𝑎𝑙𝑔⟩


-- Syntax instance for the signature
QIO:Syn : Syntax
QIO:Syn = record
  { ⅀F = ⅀F
  ; ⅀:CS = ⅀:CompatStr
  ; mvarᵢ = QIO:Terms.mvar
  ; 𝕋:Init = λ 𝔛 → let open QIO:Terms 𝔛 in record
    { ⊥ = QIO ⋉ QIOᵃ
    ; ⊥-is-initial = record { ! = λ{ {𝒜 ⋉ 𝒜ᵃ} → 𝕤𝕖𝕞 𝒜ᵃ ⋉ 𝕤𝕖𝕞ᵃ⇒ 𝒜ᵃ }
    ; !-unique = λ{ {𝒜 ⋉ 𝒜ᵃ} (f ⋉ fᵃ⇒) {x = t} → 𝕤𝕖𝕞! 𝒜ᵃ f fᵃ⇒ t } } } }

-- Instantiation of the syntax and metatheory
open Syntax QIO:Syn public
open QIO:Terms public
open import SOAS.Families.Build public
open import SOAS.Syntax.Shorthands QIOᵃ public
open import SOAS.Metatheory QIO:Syn public


