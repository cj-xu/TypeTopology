Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg and Chuangjie Xu
24 September 2026

Plump ordinals

This module is intended to develop plump ordinals as a base for the
ordinal-induced successor construction.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.Univalence

module Ordinals.Plump (ua : Univalence) where

open import UF.UA-FunExt
 using (Univalence-gives-FunExt; Univalence-gives-Fun-Ext)

fe = Univalence-gives-Fun-Ext ua
fe' = Univalence-gives-FunExt ua

open import MLTT.Spartan
open import Ordinals.Notions
open import Ordinals.Equivalence
open import Ordinals.Maps
open import Ordinals.Propositions ua
open import Ordinals.Underlying
open import Ordinals.AdditionProperties ua using (𝟘ₒ-least-⊴)
open import Ordinals.Type
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.SmallWeakPredecessors ua
import Ordinals.OrdinalOfOrdinalsWithProperty
import Ordinals.Successors
open import UF.Base
open import UF.Equiv
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import Ordinals.Arithmetic fe'
 using (𝟘ₒ; 𝟙ₒ; prop-ordinal)

\end{code}

■ Bounded comparison

We write C ≺ᵇ A when C is weakly below some ordinal strictly below A.
The superscript b stands for bounded.  The relation records an intermediate
ordinal; only its well-foundedness is needed here.

We could replace Σ by propositional existence ∃ and still prove
well-foundedness, since accessibility is a proposition.  We use Σ to avoid
assuming propositional truncations.

\begin{code}

infix 4 _≺ᵇ_

_≺ᵇ_ : Ordinal 𝓤 → Ordinal 𝓤 → 𝓤 ⁺ ̇
_≺ᵇ_ {𝓤} C A = Σ B ꞉ Ordinal 𝓤 , (C ⊴ B) × (B ⊲ A)

≺ᵇ-is-well-founded : is-well-founded (_≺ᵇ_ {𝓤})
≺ᵇ-is-well-founded {𝓤} A
 = transfinite-induction _⊲_ ⊲-is-well-founded P step A A (⊴-refl A)
 where
  P : Ordinal 𝓤 → 𝓤 ⁺ ̇
  P A = (C : Ordinal 𝓤) → C ⊴ A → is-accessible _≺ᵇ_ C

  step : (A : Ordinal 𝓤) → ((E : Ordinal 𝓤) → E ⊲ A → P E) → P A
  step A ih C h
   = acc (λ D (E , k , l) → ih E (⊲-⊴-gives-⊲ E C A l h) D k)

\end{code}

■ Plumpness

Using well-founded recursion on the bounded order ≺ᵇ, we define an ordinal A
to be plump if (1) every plump ordinal weakly below a strict predecessor of A
is itself strictly below A, and (2) every strict predecessor of A is plump.

\begin{code}

private
 plump-step
  : (A : Ordinal 𝓤)
  → ((C : Ordinal 𝓤) → C ≺ᵇ A → 𝓤 ⁺ ̇ ) → 𝓤 ⁺ ̇
 plump-step {𝓤} A below
  = ((B C : Ordinal 𝓤) → (h : C ⊴ B) → (k : B ⊲ A)
     → below C (B , h , k) → C ⊲ A)
    × ((B : Ordinal 𝓤) → (k : B ⊲ A) → below B (B , ⊴-refl B , k))

is-plump : Ordinal 𝓤 → 𝓤 ⁺ ̇
is-plump = transfinite-recursion _≺ᵇ_ ≺ᵇ-is-well-founded plump-step

is-plump-unfolding
 : (A : Ordinal 𝓤)
 → is-plump A
 ＝ (((B C : Ordinal 𝓤) → C ⊴ B → B ⊲ A → is-plump C → C ⊲ A)
    × ((B : Ordinal 𝓤) → B ⊲ A → is-plump B))
is-plump-unfolding A
 = transfinite-recursion-behaviour _≺ᵇ_ fe'
    ≺ᵇ-is-well-founded plump-step A

plump-predecessors-are-plump
 : (A B : Ordinal 𝓤) → is-plump A → B ⊲ A → is-plump B
plump-predecessors-are-plump A B p
 = pr₂ (transport (λ X → X) (is-plump-unfolding A) p) B

plump-weakly-below-predecessor-is-below
 : (A B C : Ordinal 𝓤)
 → is-plump A → C ⊴ B → B ⊲ A → is-plump C → C ⊲ A
plump-weakly-below-predecessor-is-below A B C p
 = pr₁ (transport (λ X → X) (is-plump-unfolding A) p) B C

is-plump-intro
 : (A : Ordinal 𝓤)
 → ((B C : Ordinal 𝓤) → C ⊴ B → B ⊲ A → is-plump C → C ⊲ A)
 → ((B : Ordinal 𝓤) → B ⊲ A → is-plump B)
 → is-plump A
is-plump-intro A first second
 = transport⁻¹ (λ X → X) (is-plump-unfolding A) (first , second)

is-plump-is-prop : (A : Ordinal 𝓤) → is-prop (is-plump A)
is-plump-is-prop {𝓤}
 = transfinite-induction _⊲_ ⊲-is-well-founded
    (λ A → is-prop (is-plump A)) step
 where
  step : (A : Ordinal 𝓤)
       → ((B : Ordinal 𝓤) → B ⊲ A → is-prop (is-plump B))
       → is-prop (is-plump A)
  step A ih
   = transport⁻¹ is-prop (is-plump-unfolding A)
      (×-is-prop
        (Π₅-is-prop fe (λ _ C _ _ _ → ⊲-is-prop-valued C A))
        (Π₂-is-prop fe ih))

\end{code}

■ Proposition ordinals are plump.

\begin{code}

𝟘ₒ-is-plump : is-plump (𝟘ₒ {𝓤})
𝟘ₒ-is-plump
 = is-plump-intro 𝟘ₒ
    (λ B C h (x , e) p → 𝟘-elim x)
    (λ B (x , e) → 𝟘-elim x)

prop-ordinal-is-plump : (P : 𝓤 ̇ ) (i : is-prop P)
                      → is-plump (prop-ordinal P i)
prop-ordinal-is-plump {𝓤} P i
 = is-plump-intro Pₒ claim₀ claim₁
 where
  Pₒ = prop-ordinal P i

  below-P-is-zero : {B : Ordinal 𝓤} → B ⊲ Pₒ → B ＝ 𝟘ₒ
  below-P-is-zero (p , e) = e ∙ prop-ordinal-↓ i p

  claim₀
   : (B C : Ordinal 𝓤) → C ⊴ B → B ⊲ Pₒ
   → is-plump C → C ⊲ Pₒ
  claim₀ B C h (p , e) q = p , (c-zero ∙ (prop-ordinal-↓ i p) ⁻¹)
   where
    c-to-zero : C ⊴ 𝟘ₒ
    c-to-zero = transport (C ⊴_) (below-P-is-zero (p , e)) h
    c-zero : C ＝ 𝟘ₒ
    c-zero = ⊴-antisym C 𝟘ₒ c-to-zero (𝟘ₒ-least-⊴ C)

  claim₁ : (B : Ordinal 𝓤) → B ⊲ Pₒ → is-plump B
  claim₁ B k = transport⁻¹ is-plump (below-P-is-zero k) 𝟘ₒ-is-plump

𝟙ₒ-is-plump : is-plump (𝟙ₒ {𝓤})
𝟙ₒ-is-plump = prop-ordinal-is-plump 𝟙 𝟙-is-prop

\end{code}

■ The ordinal of plump ordinals

Plump ordinals inherit the strict order on ordinals.  For extensionality,
it suffices to compare plump predecessors, since every strict predecessor
of a plump ordinal is plump.

\begin{code}

private
 module PlumpConstruction {𝓤 : Universe} where
  open Ordinals.OrdinalOfOrdinalsWithProperty.WithProperty ua
        (is-plump {𝓤}) is-plump-is-prop plump-predecessors-are-plump
   public

Plumpₒ : (𝓤 : Universe) → Ordinal (𝓤 ⁺)
Plumpₒ 𝓤 = PlumpConstruction.Pₒ {𝓤}

Plump : (𝓤 : Universe) → 𝓤 ⁺ ̇
Plump 𝓤 = ⟨ Plumpₒ 𝓤 ⟩

\end{code}

■ Mixed transitivity of plump ordinals

The internal weak order agrees with weak ordinal comparison.  Mixed
transitivity is therefore the first clause of plumpness of the upper bound.

\begin{code}

plump-≼-≺-gives-≺
 : {𝓤 : Universe} (x y z : Plump 𝓤)
 → x ≼⟨ Plumpₒ 𝓤 ⟩ y
 → y ≺⟨ Plumpₒ 𝓤 ⟩ z → x ≺⟨ Plumpₒ 𝓤 ⟩ z
plump-≼-≺-gives-≺ {𝓤} x@(A , p) y@(B , q) (C , r) h k
 = plump-weakly-below-predecessor-is-below C B A r
    (PlumpConstruction.≼-gives-⊴ x y h) k p

\end{code}

■ The plump successor

The plump successor of A consists of the plump ordinals weakly below A,
ordered by strict ordinal comparison.  It is defined for every A and lives
in the next universe.

\begin{code}

plump-succ : Ordinal 𝓤 → Ordinal (𝓤 ⁺)
plump-succ = PlumpConstruction.restricted-fat-succ

\end{code}

Every initial segment of the plump successor represents the small ordinal
indexing its endpoint.

\begin{code}

plump-succ-initial-segment
 : (A C : Ordinal 𝓤) (p : is-plump C) (h : C ⊴ A)
 → C ≃ₒ plump-succ A ↓ (C , p , h)
plump-succ-initial-segment
 = PlumpConstruction.restricted-fat-succ-initial-segment

\end{code}

■ Higher-universe plumpness implies propositional resizing

If the plump successor of 1 is plump in the next universe, every proposition
in that universe is strictly below it, which gives a small representative of
the proposition, yielding propositional resizing.

\begin{code}

plump-succ-one-is-plump-gives-propositional-resizing
 : is-plump (plump-succ (𝟙ₒ {𝓤}))
 → propositional-resizing (𝓤 ⁺) 𝓤
plump-succ-one-is-plump-gives-propositional-resizing {𝓤} s P i = p-small
 where
  S Pₒ : Ordinal (𝓤 ⁺)
  S = plump-succ (𝟙ₒ {𝓤})
  Pₒ = prop-ordinal P i

  one-in-S : ⟨ S ⟩
  one-in-S = 𝟙ₒ {𝓤} , 𝟙ₒ-is-plump , ⊴-refl 𝟙ₒ

  one-segment : 𝟙ₒ {𝓤} ≃ₒ (S ↓ one-in-S)
  one-segment
   = plump-succ-initial-segment 𝟙ₒ 𝟙ₒ 𝟙ₒ-is-plump
      (⊴-refl 𝟙ₒ)

  one-higher-segment : 𝟙ₒ {𝓤 ⁺} ≃ₒ (S ↓ one-in-S)
  one-higher-segment
   = ≃ₒ-trans (𝟙ₒ {𝓤 ⁺}) (𝟙ₒ {𝓤}) (S ↓ one-in-S)
      only-one-𝟙ₒ one-segment

  one-below : 𝟙ₒ {𝓤 ⁺} ⊲ S
  one-below
   = ⌜ ⊲-is-equivalent-to-⊲⁻ (𝟙ₒ {𝓤 ⁺}) S ⌝⁻¹
      (one-in-S , one-higher-segment)

  -- The plumpness of plump-succ (𝟙ₒ {𝓤}) implies
  --
  --   P ⊲ plump-succ (𝟙ₒ {𝓤})
  --
  -- for any proposition P in 𝓤 ⁺.
  p-below : Pₒ ⊲ S
  p-below
   = plump-weakly-below-predecessor-is-below S 𝟙ₒ Pₒ s
      (prop-ordinal-⊴ i 𝟙-is-prop (λ _ → ⋆)) one-below
      (prop-ordinal-is-plump P i)

  -- Therefore, there is a representative of P in plump-succ (𝟙ₒ {𝓤}),
  -- which is small, i.e., living in 𝓤.
  x : ⟨ S ⟩
  x = pr₁ p-below

  C : Ordinal 𝓤
  C = pr₁ x

  c-equiv-p : C ≃ₒ Pₒ
  c-equiv-p
   = transport⁻¹ (C ≃ₒ_) (pr₂ p-below)
      (plump-succ-initial-segment 𝟙ₒ C (pr₁ (pr₂ x)) (pr₂ (pr₂ x)))

  p-small : P is 𝓤 small
  p-small = ⟨ C ⟩ , ≃ₒ-gives-≃ C Pₒ c-equiv-p

\end{code}

■ The small plump successor

Given propositional resizing and small representatives for weak predecessors,
we instantiate the small restricted fat successor construction.  Its strict
predecessors are exactly the plump ordinals weakly below its input.

\begin{code}

module WithResizing
        {𝓤 : Universe}
        (ρ : propositional-resizing (𝓤 ⁺) 𝓤)
        (weak-predecessors-are-small : Weak-predecessors-are-small)
       where

 private
  module SmallConstruction
   = Ordinals.OrdinalOfOrdinalsWithProperty.WithPropertyAndResizing ua
      (is-plump {𝓤}) is-plump-is-prop plump-predecessors-are-plump ρ
      weak-predecessors-are-small

 plump-succ-small : Ordinal 𝓤 → Ordinal 𝓤
 plump-succ-small = SmallConstruction.restricted-fat-succ-small

 plump-succ-small-≃ₒ-plump-succ
  : (A : Ordinal 𝓤) → plump-succ-small A ≃ₒ plump-succ A
 plump-succ-small-≃ₒ-plump-succ
  = SmallConstruction.restricted-fat-succ-small-≃ₒ-restricted-fat-succ

 ⊲-plump-succ-small-gives-plump-and-⊴
  : (A C : Ordinal 𝓤)
  → C ⊲ plump-succ-small A → is-plump C × (C ⊴ A)
 ⊲-plump-succ-small-gives-plump-and-⊴
  = SmallConstruction.⊲-restricted-fat-succ-small-gives-P-and-⊴

 plump-and-⊴-gives-⊲-plump-succ-small
  : (A C : Ordinal 𝓤)
  → is-plump C × (C ⊴ A) → C ⊲ plump-succ-small A
 plump-and-⊴-gives-⊲-plump-succ-small
  = SmallConstruction.P-and-⊴-gives-⊲-restricted-fat-succ-small

\end{code}

The small plump successor is plump for every input.

\begin{code}

 plump-succ-small-is-plump
  : (A : Ordinal 𝓤) → is-plump (plump-succ-small A)
 plump-succ-small-is-plump A
  = is-plump-intro S claim₀ claim₁
  where
   S = plump-succ-small A

   claim₀
    : (B C : Ordinal 𝓤) → C ⊴ B → B ⊲ S → is-plump C → C ⊲ S
   claim₀ B C h k p = plump-and-⊴-gives-⊲-plump-succ-small A C (p , j)
    where
     i : B ⊴ A
     i = pr₂ (⊲-plump-succ-small-gives-plump-and-⊴ A B k)
     j : C ⊴ A
     j = ⊴-trans C B A h i

   claim₁ : (B : Ordinal 𝓤) → B ⊲ S → is-plump B
   claim₁ B k = pr₁ (⊲-plump-succ-small-gives-plump-and-⊴ A B k)

\end{code}

■ An internal exact and strong successor

Pairing the small successor with its plumpness proof gives an exact and
strong successor in Plumpₒ.

\begin{code}

 open Ordinals.Successors.Successors ua (Plumpₒ 𝓤)
  using (_is-exact-succ-of_; _is-strong-succ-of_;
         exact-succ-gives-strong-succ)

 internal-plump-succ : Plump 𝓤 → Plump 𝓤
 internal-plump-succ (A , _)
  = plump-succ-small A , plump-succ-small-is-plump A

 internal-plump-succ-is-exact-succ
  : (x : Plump 𝓤) → (internal-plump-succ x) is-exact-succ-of x
 internal-plump-succ-is-exact-succ x@(A , p) y@(C , q)
  = (λ h → SmallConstruction.⊴-gives-≼ y x
             (pr₂ (⊲-plump-succ-small-gives-plump-and-⊴ A C h))) ,
    (λ h → plump-and-⊴-gives-⊲-plump-succ-small A C
             (q , SmallConstruction.≼-gives-⊴ y x h))

 internal-plump-succ-is-strong-succ
  : (x : Plump 𝓤) → (internal-plump-succ x) is-strong-succ-of x
 internal-plump-succ-is-strong-succ x
  = exact-succ-gives-strong-succ plump-≼-≺-gives-≺
     (internal-plump-succ x) x (internal-plump-succ-is-exact-succ x)

\end{code}
