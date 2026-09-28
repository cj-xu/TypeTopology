Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg and Chuangjie Xu
24 September 2026

Plump ordinals

We define plumpness by well-founded recursion on bounded comparison and form
the ordinal of plump ordinals, and then construct the large plump successor and,
under resizing assumptions, a small internal strong and exact successor.

The notion of plump ordinal and the plump successor are due to Paul Taylor
[1].  Our formulation adapts Taylor's set-theoretic development to ordinals
in univalent type theory.

[1] Paul Taylor. Intuitionistic sets and ordinals. The Journal of Symbolic
    Logic, 61(3):705–744, 1996. https://doi.org/10.2307/2275781

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.Univalence

module Ordinals.Plump (ua : Univalence) where

open import UF.UA-FunExt
 using (Univalence-gives-FunExt; Univalence-gives-Fun-Ext)

private
 fe = Univalence-gives-Fun-Ext ua
 fe' = Univalence-gives-FunExt ua

open import MLTT.Spartan
open import Ordinals.Notions
open import Ordinals.Equivalence
open import Ordinals.Maps
open import Ordinals.Propositions ua
open import Ordinals.Underlying
open import Ordinals.AdditionProperties ua
 using (+ₒ-↓-left; successor-lemma-right;
        𝟘ₒ-least-⊴)
open import Ordinals.Type
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.SmallWeakPredecessors ua
open import Ordinals.WellOrderTransport fe'
import Ordinals.OrdinalOfOrdinalsWithProperty
import Ordinals.InducedSuccessor
import Ordinals.Successors
open import UF.Base
open import UF.ClassicalLogic
open import UF.Equiv
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import Ordinals.Arithmetic fe'
 using (_+ₒ_; 𝟘ₒ; 𝟙ₒ; prop-ordinal)

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

■ Proposition ordinals are plump

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

■ Ordinal mixed transitivity and universal plumpness

Ordinal mixed transitivity is equivalent to excluded middle.  The same is
true of the statement that every ordinal is plump.

\begin{code}

private
 ⊲⁻-is-well-order : is-well-order {𝓤 ⁺} {𝓤} _⊲⁻_
 ⊲⁻-is-well-order {𝓤}
  = order-transfer-lemma₃.well-order→ (Ordinal 𝓤) _⊲_ _⊲⁻_
     ⊲-is-equivalent-to-⊲⁻ ⊲-is-well-order

EM-implies-⊴-⊲-gives-⊲
 : EM 𝓤
 → (C B A : Ordinal 𝓤) → C ⊴ B → B ⊲ A → C ⊲ A
EM-implies-⊴-⊲-gives-⊲ em C B A h k
 = analyze (trichotomy₃ _⊲⁻_ em ⊲⁻-is-well-order C B)
 where
  analyze : (C ⊲⁻ B) + (C ＝ B) + (B ⊲⁻ C) → C ⊲ A
  analyze (inl l)
   = ⊲-is-transitive C B A (⌜ ⊲-is-equivalent-to-⊲⁻ C B ⌝⁻¹ l) k
  analyze (inr (inl e)) = transport⁻¹ (_⊲ A) e k
  analyze (inr (inr l))
   = 𝟘-elim
      (⊴-gives-not-⊲ C B h (⌜ ⊲-is-equivalent-to-⊲⁻ B C ⌝⁻¹ l))

⊴-⊲-gives-⊲-implies-EM
 : ((C B A : Ordinal 𝓤) → C ⊴ B → B ⊲ A → C ⊲ A)
 → EM 𝓤
⊴-⊲-gives-⊲-implies-EM {𝓤} mixed P P-is-prop
 = decide (mixed Pₒ 𝟙ₒ 𝟚ₒ P-below-one one-below-two)
 where
  Pₒ = prop-ordinal P P-is-prop
  𝟚ₒ = 𝟙ₒ {𝓤} +ₒ 𝟙ₒ

  P-below-one : Pₒ ⊴ 𝟙ₒ
  P-below-one = prop-ordinal-⊴ P-is-prop 𝟙-is-prop (λ _ → ⋆)

  one-below-two : 𝟙ₒ ⊲ 𝟚ₒ
  one-below-two = inr ⋆ , ((successor-lemma-right 𝟙ₒ) ⁻¹)

  decide : Pₒ ⊲ 𝟚ₒ → P + ¬ P
  decide (inl ⋆ , e) = inr does-not-hold
   where
    p-zero : Pₒ ＝ 𝟘ₒ
    p-zero = e ∙ (+ₒ-↓-left ⋆) ⁻¹ ∙ 𝟙ₒ-↓

    does-not-hold : ¬ P
    does-not-hold = equal-𝟘-is-empty (ap ⟨_⟩ p-zero)
  decide (inr ⋆ , e) = inl (transport⁻¹ ⟨_⟩ p-one ⋆)
   where
    p-one : Pₒ ＝ 𝟙ₒ
    p-one = e ∙ successor-lemma-right 𝟙ₒ

ordinal-mixed-transitivity-iff-EM
 : ((C B A : Ordinal 𝓤) → C ⊴ B → B ⊲ A → C ⊲ A) ↔ EM 𝓤
ordinal-mixed-transitivity-iff-EM
 = ⊴-⊲-gives-⊲-implies-EM , EM-implies-⊴-⊲-gives-⊲

EM-implies-all-ordinals-are-plump
 : EM 𝓤 → (A : Ordinal 𝓤) → is-plump A
EM-implies-all-ordinals-are-plump {𝓤} em
 = transfinite-induction _⊲_ ⊲-is-well-founded is-plump step
 where
  step : (A : Ordinal 𝓤)
       → ((B : Ordinal 𝓤) → B ⊲ A → is-plump B)
       → is-plump A
  step A ih = is-plump-intro A claim ih
   where
    claim : (B C : Ordinal 𝓤) → C ⊴ B → B ⊲ A
          → is-plump C → C ⊲ A
    claim B C h k _ = EM-implies-⊴-⊲-gives-⊲ em C B A h k

all-ordinals-are-plump-implies-EM
 : ((A : Ordinal 𝓤) → is-plump A) → EM 𝓤
all-ordinals-are-plump-implies-EM {𝓤} all-plump
 = ⊴-⊲-gives-⊲-implies-EM mixed
 where
  mixed : (C B A : Ordinal 𝓤) → C ⊴ B → B ⊲ A → C ⊲ A
  mixed C B A h k
   = plump-weakly-below-predecessor-is-below A B C
       (all-plump A) h k (all-plump C)

all-ordinals-are-plump-iff-EM
 : ((A : Ordinal 𝓤) → is-plump A) ↔ EM 𝓤
all-ordinals-are-plump-iff-EM
 = all-ordinals-are-plump-implies-EM ,
   EM-implies-all-ordinals-are-plump

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

plump-ordinal-representation
 : (A : Ordinal 𝓤) (p : is-plump A)
 → A ≃ₒ (Plumpₒ 𝓤 ↓ (A , p))
plump-ordinal-representation A p
 = PlumpConstruction.ordinals-in-Pₒ-are-lowersets-of-Pₒ (A , p)

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

■ Splitting the weak order of plump ordinals

The weak order on plump ordinals splits into strict comparison or equality
exactly when excluded middle holds.

\begin{code}

module _ {𝓤 : Universe} where

 open Ordinals.InducedSuccessor.InducedSuccessor ua (Plumpₒ 𝓤)
  using (Weak-order-splits)

 plump-weak-order-splits-implies-EM
  : Weak-order-splits → EM 𝓤
 plump-weak-order-splits-implies-EM splits P P-is-prop
  = decide (splits x y x-weakly-below-y)
  where
   Pₒ = prop-ordinal P P-is-prop

   x y : Plump 𝓤
   x = Pₒ , prop-ordinal-is-plump P P-is-prop
   y = 𝟙ₒ , 𝟙ₒ-is-plump

   x-weakly-below-y : x ≼⟨ Plumpₒ 𝓤 ⟩ y
   x-weakly-below-y
    = PlumpConstruction.⊴-gives-≼ x y
       (prop-ordinal-⊴ P-is-prop 𝟙-is-prop (λ _ → ⋆))

   decide : (x ≺⟨ Plumpₒ 𝓤 ⟩ y) + (x ＝ y) → P + ¬ P
   decide (inl (⋆ , e)) = inr does-not-hold
    where
     P-is-zero : Pₒ ＝ 𝟘ₒ
     P-is-zero = e ∙ 𝟙ₒ-↓
     does-not-hold : ¬ P
     does-not-hold = equal-𝟘-is-empty (ap ⟨_⟩ P-is-zero)
   decide (inr e) = inl (transport⁻¹ ⟨_⟩ (ap pr₁ e) ⋆)

 EM-implies-plump-weak-order-splits
  : EM 𝓤 → Weak-order-splits
 EM-implies-plump-weak-order-splits em x@(A , p) y@(B , q) h
  = decide (trichotomy₃ _⊲⁻_ em ⊲⁻-is-well-order A B)
  where
   A-weakly-below-B : A ⊴ B
   A-weakly-below-B = PlumpConstruction.≼-gives-⊴ x y h

   decide : (A ⊲⁻ B) + (A ＝ B) + (B ⊲⁻ A)
          → (x ≺⟨ Plumpₒ 𝓤 ⟩ y) + (x ＝ y)
   decide (inl l)
    = inl (⌜ ⊲-is-equivalent-to-⊲⁻ A B ⌝⁻¹ l)
   decide (inr (inl e))
    = inr (to-subtype-＝ is-plump-is-prop e)
   decide (inr (inr l))
    = 𝟘-elim
       (⊴-gives-not-⊲ A B A-weakly-below-B
        (⌜ ⊲-is-equivalent-to-⊲⁻ B A ⌝⁻¹ l))

 plump-weak-order-splits-iff-EM
  : Weak-order-splits ↔ EM 𝓤
 plump-weak-order-splits-iff-EM
  = plump-weak-order-splits-implies-EM ,
    EM-implies-plump-weak-order-splits

\end{code}

■ The plump successor

The plump successor of A consists of the plump ordinals weakly below A,
ordered by strict ordinal comparison.  It is the restricted fat successor
for the property of being plump.  It is defined for every A and lives in the
next universe.

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

■ Higher-universe plumpness of plump successors implies propositional resizing

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
