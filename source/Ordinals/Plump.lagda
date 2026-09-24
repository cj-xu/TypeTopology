Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg and Chuangjie Xu
24 September 2026

Plump ordinals

This module is intended to develop plump ordinals as a base for the
ordinal-induced successor construction.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.Univalence

module Ordinals.Plump (ua : Univalence) where

open import MLTT.Spartan
open import Ordinals.Notions
open import Ordinals.Equivalence
open import Ordinals.Maps
open import Ordinals.Propositions ua
open import Ordinals.Underlying
open import Ordinals.AdditionProperties ua using (𝟘ₒ-least-⊴)
open import Ordinals.Type
open import Ordinals.OrdinalOfOrdinals ua
import Ordinals.OrdinalOfOrdinalsWithProperty
import Ordinals.Successors
open import UF.Base
open import UF.Equiv
open import UF.Size using (propositional-resizing; Propositional-Resizing)
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt
 using (Univalence-gives-FunExt; Univalence-gives-Fun-Ext)
open import Ordinals.Arithmetic (Univalence-gives-FunExt ua)
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

We define plumpness by two requirements.  First, every plump ordinal weakly
below a strict predecessor of A is itself strictly below A.  Second, every
strict predecessor of A is plump.

\begin{code}

private
 plump-step : (A : Ordinal 𝓤)
            → ((C : Ordinal 𝓤) → C ≺ᵇ A → 𝓤 ⁺ ̇ ) → 𝓤 ⁺ ̇
 plump-step {𝓤} A below
  = ((B C : Ordinal 𝓤) → (h : C ⊴ B) → (k : B ⊲ A)
     → below C (B , h , k) → C ⊲ A)
    × ((B : Ordinal 𝓤) → (k : B ⊲ A) → below B (B , ⊴-refl B , k))

isPlump : Ordinal 𝓤 → 𝓤 ⁺ ̇
isPlump = transfinite-recursion _≺ᵇ_ ≺ᵇ-is-well-founded plump-step

isPlump-unfolding
 : (A : Ordinal 𝓤)
 → isPlump A ＝ ((B C : Ordinal 𝓤) → C ⊴ B → B ⊲ A → isPlump C → C ⊲ A)
              × ((B : Ordinal 𝓤) → B ⊲ A → isPlump B)
isPlump-unfolding A
 = transfinite-recursion-behaviour _≺ᵇ_ (Univalence-gives-FunExt ua)
    ≺ᵇ-is-well-founded plump-step A

plump-predecessors-are-plump : (A B : Ordinal 𝓤)
                             → isPlump A → B ⊲ A → isPlump B
plump-predecessors-are-plump A B p
 = pr₂ (transport (λ X → X) (isPlump-unfolding A) p) B

\end{code}

Plumpness is proposition-valued by induction on the strict order.

\begin{code}

isPlump-is-prop : (A : Ordinal 𝓤) → is-prop (isPlump A)
isPlump-is-prop {𝓤}
 = transfinite-induction _⊲_ ⊲-is-well-founded
    (λ A → is-prop (isPlump A)) step
 where
  fe = Univalence-gives-FunExt ua

  step : (A : Ordinal 𝓤)
       → ((B : Ordinal 𝓤) → B ⊲ A → is-prop (isPlump B))
       → is-prop (isPlump A)
  step A ih
   = transport⁻¹ is-prop (isPlump-unfolding A)
      (×-is-prop
        (Π-is-prop (fe _ _) (λ B → Π-is-prop (fe _ _) (λ C →
         Π-is-prop (fe _ _) (λ h → Π-is-prop (fe _ _) (λ k →
         Π-is-prop (fe _ _) (λ p → ⊲-is-prop-valued C A))))))
        (Π-is-prop (fe _ _) (λ B → Π-is-prop (fe _ _) (ih B))))

\end{code}

■ Proposition ordinals are plump

The empty ordinal is plump vacuously.  Every strict predecessor of a
proposition ordinal is empty, so proposition ordinals are also plump.

\begin{code}

𝟘ₒ-is-plump : isPlump (𝟘ₒ {𝓤})
𝟘ₒ-is-plump
 = transport⁻¹ (λ X → X) (isPlump-unfolding 𝟘ₒ)
    ((λ B C h (x , e) p → 𝟘-elim x) , (λ B (x , e) → 𝟘-elim x))

prop-ordinal-is-plump : (P : 𝓤 ̇ ) (i : is-prop P)
                      → isPlump (prop-ordinal P i)
prop-ordinal-is-plump {𝓤} P i
 = transport⁻¹ (λ X → X) (isPlump-unfolding A) (first , second)
 where
  A = prop-ordinal P i

  first : (B C : Ordinal 𝓤) → C ⊴ B → B ⊲ A → isPlump C → C ⊲ A
  first B C h (p , e) q = p , (c-empty ∙ (prop-ordinal-↓ i p) ⁻¹)
   where
    b-empty : B ＝ 𝟘ₒ
    b-empty = e ∙ prop-ordinal-↓ i p

    c-empty : C ＝ 𝟘ₒ
    c-empty = ⊴-antisym C 𝟘ₒ (transport (C ⊴_) b-empty h) (𝟘ₒ-least-⊴ C)

  second : (B : Ordinal 𝓤) → B ⊲ A → isPlump B
  second B (p , e)
   = transport⁻¹ isPlump (e ∙ prop-ordinal-↓ i p) 𝟘ₒ-is-plump

\end{code}

■ The ordinal of plump ordinals

Plump ordinals inherit the strict order on ordinals.  For extensionality,
it suffices to compare plump predecessors, since every strict predecessor
of a plump ordinal is plump.

\begin{code}

module PlumpOrdinals (𝓤 : Universe) where
 module Construction
  = Ordinals.OrdinalOfOrdinalsWithProperty.WithProperty ua
     (isPlump {𝓤}) isPlump-is-prop plump-predecessors-are-plump

Plump : (𝓤 : Universe) → 𝓤 ⁺ ̇
Plump 𝓤 = PlumpOrdinals.Construction.Ordinals-with-property 𝓤

infix 4 _⊲ᵖ_

_⊲ᵖ_ : Plump 𝓤 → Plump 𝓤 → 𝓤 ⁺ ̇
_⊲ᵖ_ {𝓤} = PlumpOrdinals.Construction.property-order 𝓤

Plumpₒ : (𝓤 : Universe) → Ordinal (𝓤 ⁺)
Plumpₒ 𝓤 = PlumpOrdinals.Construction.Pₒ 𝓤

\end{code}

■ The plump successor

The plump successor of A consists of the plump ordinals weakly below A,
ordered by strict ordinal comparison.  It is defined for every A and lives
in the next universe.

\begin{code}

plump-succ : Ordinal 𝓤 → Ordinal (𝓤 ⁺)
plump-succ {𝓤} = PlumpOrdinals.Construction.direct-succ 𝓤

\end{code}

Every initial segment of the plump successor represents the small ordinal
indexing its endpoint.  The canonical map to OO preserves these segments.

\begin{code}

plump-succ-⊴-OO : (A : Ordinal 𝓤) → plump-succ A ⊴ OO 𝓤
plump-succ-⊴-OO {𝓤} A = pr₁ , initial , (λ x y l → l)
 where
  initial : is-initial-segment (plump-succ A) (OO 𝓤) pr₁
  initial (C , p , h) D l
   = (D , plump-predecessors-are-plump C D p l ,
          ⊴-trans D C A (⊲-gives-⊴ D C l) h) , l , refl

plump-succ-initial-segment
 : (A C : Ordinal 𝓤) (p : isPlump C) (h : C ⊴ A)
 → C ≃ₒ (plump-succ A ↓ (C , p , h))
plump-succ-initial-segment {𝓤} A C p h
 = ≃ₒ-trans C (OO 𝓤 ↓ C) (plump-succ A ↓ (C , p , h))
    (ordinals-in-OO-are-lowersets-of-OO C)
    (simulations-pointwise-equal-gives-isomorphic-initial-segments
      (OO 𝓤) (plump-succ A) (OO 𝓤)
      (⊴-refl (OO 𝓤)) (plump-succ-⊴-OO A) C (C , p , h) refl)

\end{code}

■ Higher-universe plumpness implies propositional resizing

If the plump successor of 1 is plump in the next universe, every proposition
in that universe is one of its strict predecessors.  Each such predecessor
has a small representative, yielding propositional resizing.

\begin{code}

plump-succ-one-is-plump-gives-propositional-resizing
 : isPlump (plump-succ (𝟙ₒ {𝓤})) → propositional-resizing (𝓤 ⁺) 𝓤
plump-succ-one-is-plump-gives-propositional-resizing {𝓤} s P i
 = ⟨ C ⟩ , ≃ₒ-gives-≃ C Q c-equiv-q
 where
  S = plump-succ (𝟙ₒ {𝓤})
  Q = prop-ordinal P i

  one-plump : isPlump (𝟙ₒ {𝓤})
  one-plump = prop-ordinal-is-plump 𝟙 𝟙-is-prop

  one-below : 𝟙ₒ {𝓤 ⁺} ⊲ S
  one-below
   = ⌜ ⊲-is-equivalent-to-⊲⁻ (𝟙ₒ {𝓤 ⁺}) S ⌝⁻¹
      ((𝟙ₒ , one-plump , ⊴-refl 𝟙ₒ) ,
       ≃ₒ-trans (𝟙ₒ {𝓤 ⁺}) (𝟙ₒ {𝓤})
        (S ↓ (𝟙ₒ , one-plump , ⊴-refl 𝟙ₒ)) only-one-𝟙ₒ
        (plump-succ-initial-segment 𝟙ₒ 𝟙ₒ one-plump (⊴-refl 𝟙ₒ)))

  q-below : Q ⊲ S
  q-below
   = pr₁ (transport (λ X → X) (isPlump-unfolding S) s)
      𝟙ₒ Q (prop-ordinal-⊴ i 𝟙-is-prop (λ _ → ⋆)) one-below
      (prop-ordinal-is-plump P i)

  x : ⟨ S ⟩
  x = pr₁ q-below

  C : Ordinal 𝓤
  C = pr₁ x

  c-equiv-q : C ≃ₒ Q
  c-equiv-q
   = transport⁻¹ (C ≃ₒ_) (pr₂ q-below)
      (plump-succ-initial-segment 𝟙ₒ C (pr₁ (pr₂ x)) (pr₂ (pr₂ x)))

\end{code}

■ Mixed transitivity of plump ordinals

The internal weak order agrees with weak ordinal comparison.  Mixed
transitivity is therefore the first clause of plumpness of the upper bound.

\begin{code}

plump-mixed-transitivity
 : {𝓤 : Universe} (x y z : Plump 𝓤)
 → x ≼⟨ Plumpₒ 𝓤 ⟩ y
 → y ≺⟨ Plumpₒ 𝓤 ⟩ z → x ≺⟨ Plumpₒ 𝓤 ⟩ z
plump-mixed-transitivity {𝓤} x@(A , p) y@(B , q) (C , r) h k
 = pr₁ (transport (λ X → X) (isPlump-unfolding C) r) B A
    (PlumpOrdinals.Construction.≼-gives-⊴ 𝓤 x y h) k p

\end{code}
