Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg and Chuangjie Xu
24 September 2026

Examples of ordinal-induced successors

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.Univalence

module Ordinals.InducedSuccessorExamples (ua : Univalence) where

open import MLTT.Spartan
import Ordinals.CantorNormalForm
import Ordinals.OrdinalOfOrdinalsWithProperty
import Ordinals.Plump
open import Ordinals.InducedSuccessor ua
open import Ordinals.SmallWeakPredecessors ua
open import Ordinals.Successors ua
open import Ordinals.Type
open import Ordinals.Underlying
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.AdditionProperties ua
 using (𝟘ₒ-least-⊴; 𝟘ₒ-left-neutral)
open import UF.UA-FunExt using (Univalence-gives-FunExt)
open import Ordinals.Arithmetic (Univalence-gives-FunExt ua)
 using (𝟘ₒ; 𝟙ₒ)
open import UF.ClassicalLogic
open import UF.Size using (propositional-resizing)
open import UF.Subsingletons


\end{code}

■ Cantor normal forms

We take the ordinal Cnfₒ of Cantor normal forms (CNFs) as the base.

Its trichotomous order and internal successor supply the conditions needed for
the general characterization theorems.

\begin{code}

module CantorNormalForms where

 module CNF = Ordinals.CantorNormalForm
 open CNF using (Cnf; Cnfₒ)
 open InducedSuccessor Cnfₒ public

\end{code}

Recall that the weak order of CNFs has mixed transitivity and splits into
strict comparison or equality, and that the every CNF has a strong and exact
successor.

\begin{code}

 mixed-transitivity : Mixed-transitivity
 mixed-transitivity = CNF.≼-<-gives-<

 weak-order-splits : Weak-order-splits
 weak-order-splits x y h = split (CNF.≼-gives-≦ h)
  where
   split : x CNF.≦ y → (x ≺ᴮ y) + (x ＝ y)
   split (inl l) = inl l
   split (inr e) = inr (e ⁻¹)

 strong-successor : calc-strong-succ CNF.succ
 strong-successor = CNF.succ-is-strong-succ ua

 exact-successors : Has-exact-successors
 exact-successors x = CNF.succ x , CNF.succ-is-exact-succ ua x

 bounded-elements-have-successors : Bounded-elements-have-successors
 bounded-elements-have-successors x y h
  = CNF.succ x , strong-succ-gives-succ (CNF.succ x) x (strong-successor x)

\end{code}

Therefore, the successor induced by Cnfₒ has all the desired properties.

\begin{code}

 relative-leastness : Induced-succ-relative-leastness
 relative-leastness
  = mixed-transitivity-gives-induced-succ-relative-leastness mixed-transitivity

 commutes-with-successor : Induced-succ-commutes-with CNF.succ
 commutes-with-successor
  = mixed-transitivity-gives-induced-succ-commutation
     CNF.succ strong-successor mixed-transitivity

 strict-monotonicity : Induced-succ-strict-monotonicity
 strict-monotonicity
  = mixed-transitivity-and-bounded-successors-give-strict-monotonicity
     (mixed-transitivity , bounded-elements-have-successors)

 closure : Induced-succ-closure
 closure = has-exact-successors-gives-induced-succ-closure exact-successors

\end{code}

For inputs strictly below Cnfₒ, the induced successor coincides with the thin
successor.  However, for fat successor, this is equivalent to excluded middle.

\begin{code}

 below-thin : Induced-succ-below-thin
 below-thin
  = weak-order-splits-gives-induced-succ-⊴-thin-succ
     weak-order-splits

 induced-succ-equals-thin : (A : Ordinal 𝓤₀) → A ⊲ Cnfₒ
                          → induced-succ A ＝ thin-succ A
 induced-succ-equals-thin A h
  = ⊴-antisym (induced-succ A) (thin-succ A)
     (below-thin A h) (thin-succ-⊴-induced-succ A h)

 private
  zero-segment : Cnfₒ ↓ CNF.𝟎 ＝ 𝟘ₒ
  zero-segment = ⊴-antisym (Cnfₒ ↓ CNF.𝟎) 𝟘ₒ
                  (f , (λ u → 𝟘-elim (f u)) , (λ u → 𝟘-elim (f u)))
                  (𝟘ₒ-least-⊴ (Cnfₒ ↓ CNF.𝟎))
   where
    f : (Σ x ꞉ Cnf , x CNF.< CNF.𝟎) → 𝟘
    f (x , ())

  one-below-base : 𝟙ₒ ⊲ Cnfₒ
  one-below-base = CNF.succ CNF.𝟎 , (q ⁻¹)
   where
    q : Cnfₒ ↓ CNF.succ CNF.𝟎 ＝ 𝟙ₒ
    q = commutes-with-successor CNF.𝟎
        ∙ induced-succ-equals-thin (Cnfₒ ↓ CNF.𝟎) (CNF.𝟎 , refl)
        ∙ ap thin-succ zero-segment ∙ 𝟘ₒ-left-neutral 𝟙ₒ

 fat-below-induced-gives-EM : Fat-succ-below-induced → EM 𝓤₀
 fat-below-induced-gives-EM comparison
  = fat-succ-one-⊴-thin-succ-one-gives-EM
     (⊴-trans (fat-succ 𝟙ₒ) (induced-succ 𝟙ₒ) (thin-succ 𝟙ₒ)
       (comparison 𝟙ₒ one-below-base) (below-thin 𝟙ₒ one-below-base))

 EM-gives-fat-below-induced : EM 𝓤₀ → Fat-succ-below-induced
 EM-gives-fat-below-induced em A h
  = transport⁻¹ (fat-succ A ⊴_) (induced-succ-equals-thin A h)
     (EM-gives-fat-succ-⊴-thin-succ em A)

 fat-below-induced-iff-EM : Fat-succ-below-induced ↔ EM 𝓤₀
 fat-below-induced-iff-EM
  = fat-below-induced-gives-EM , EM-gives-fat-below-induced

 external-mixed-transitivity-iff-EM
  : External-mixed-transitivity-below-base ↔ EM 𝓤₀
 external-mixed-transitivity-iff-EM
  = ↔-trans
     (↔-sym
       fat-succ-⊴-induced-succ-iff-external-mixed-transitivity-below-base)
     fat-below-induced-iff-EM

\end{code}

■ Plump ordinals

We take the ordinal of plump ordinals as the base.

\begin{code}

module PlumpOrdinals {𝓤 : Universe} where

 module Plump = Ordinals.Plump ua

 open Plump using (Plumpₒ; is-plump; plump-succ)
 open InducedSuccessor (Plumpₒ 𝓤) public

 private
  module Construction
   = Ordinals.OrdinalOfOrdinalsWithProperty.WithProperty ua
      (is-plump {𝓤}) Plump.is-plump-is-prop
      Plump.plump-predecessors-are-plump

\end{code}

The large plump successor of a plump ordinal is the successor induced at its
initial segment in the ordinal of plump ordinals.  It therefore shares the
corresponding properties of the induced successor.

\begin{code}

 plump-succ-equals-induced-succ
  : (A : Ordinal 𝓤) (p : is-plump A)
  → plump-succ A ＝ induced-succ (Plumpₒ 𝓤 ↓ (A , p))
 plump-succ-equals-induced-succ
  = Construction.restricted-fat-succ-equals-induced-succ

\end{code}

The internal order of plump ordinals has mixed transitivity.  Consequently,
the induced successor has relative leastness without any resizing assumption.

\begin{code}

 mixed-transitivity : Mixed-transitivity
 mixed-transitivity = Plump.plump-≼-≺-gives-≺

 relative-leastness : Induced-succ-relative-leastness
 relative-leastness
  = mixed-transitivity-gives-induced-succ-relative-leastness
     mixed-transitivity

\end{code}

Under propositional resizing and smallness of weak predecessors, the small
plump successor gives an internal exact and strong successor.  The general
characterizations then give commutation, strict monotonicity, and closure of
the induced successor.

\begin{code}

 module WithResizing
         (ρ : propositional-resizing (𝓤 ⁺) 𝓤)
         (weak-predecessors-are-small : Weak-predecessors-are-small {𝓤})
        where

  private
   module Small
    = Plump.WithResizing ρ weak-predecessors-are-small

  internal-successor : Plump.Plump 𝓤 → Plump.Plump 𝓤
  internal-successor = Small.internal-plump-succ

  strong-successor : calc-strong-succ internal-successor
  strong-successor = Small.internal-plump-succ-is-strong-succ

  exact-successors : Has-exact-successors
  exact-successors x
   = internal-successor x , Small.internal-plump-succ-is-exact-succ x

  bounded-elements-have-successors : Bounded-elements-have-successors
  bounded-elements-have-successors x y h
   = internal-successor x ,
     strong-succ-gives-succ
      (internal-successor x) x (strong-successor x)

  commutes-with-successor
   : Induced-succ-commutes-with internal-successor
  commutes-with-successor
   = mixed-transitivity-gives-induced-succ-commutation
      internal-successor strong-successor mixed-transitivity

  strict-monotonicity : Induced-succ-strict-monotonicity
  strict-monotonicity
   = mixed-transitivity-and-bounded-successors-give-strict-monotonicity
      (mixed-transitivity , bounded-elements-have-successors)

  closure : Induced-succ-closure
  closure
   = has-exact-successors-gives-induced-succ-closure exact-successors

\end{code}
