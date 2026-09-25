Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg and Chuangjie Xu
25 September 2026

Small weak predecessors

We state the common interface for constructions that represent the weak
predecessors of every ordinal by a type in the same universe.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.Univalence

module Ordinals.SmallWeakPredecessors (ua : Univalence) where

open import MLTT.Spartan
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.Type
open import UF.Size

Weak-predecessors : Ordinal 𝓤 → 𝓤 ⁺ ̇
Weak-predecessors {𝓤} A = Σ C ꞉ Ordinal 𝓤 , C ⊴ A

Weak-predecessors-are-small : 𝓤 ⁺ ̇
Weak-predecessors-are-small {𝓤}
 = (A : Ordinal 𝓤) → Weak-predecessors A is 𝓤 small

\end{code}
