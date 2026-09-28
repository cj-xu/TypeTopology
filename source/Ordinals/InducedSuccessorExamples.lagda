Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg and Chuangjie Xu
24 September 2026

Examples of ordinal-induced successors

We apply the general theory of induced successors to Cantor normal forms and
plump ordinals.  For each base, we derive properties of the induced successor
from the order-theoretic structure available in that example and compare it
with the corresponding concrete successors.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.Univalence

module Ordinals.InducedSuccessorExamples (ua : Univalence) where

open import MLTT.Spartan
import Ordinals.CantorNormalForm
import Ordinals.OrdinalOfOrdinalsWithProperty
import Ordinals.Plump
open import Ordinals.Equivalence
open import Ordinals.InducedSuccessor ua
open import Ordinals.SmallWeakPredecessors ua
open import Ordinals.Successors ua
open import Ordinals.Type
open import Ordinals.Underlying
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.AdditionProperties ua
 using (𝟘ₒ-least-⊴; 𝟘ₒ-left-neutral)
open import UF.UA-FunExt
 using (Univalence-gives-FunExt; Univalence-gives-Fun-Ext)
open import Ordinals.Arithmetic (Univalence-gives-FunExt ua)
 using (𝟘ₒ; 𝟙ₒ)
open import UF.Base using (transport₂)
open import UF.ClassicalLogic
open import UF.Size using (propositional-resizing)

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

The weak order of CNFs has mixed transitivity and splits into strict comparison
or equality.  Moreover, every CNF has a strong and exact successor.

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

It follows that the induced successor has relative leastness, commutes with the
CNF successor, is strictly monotone below Cnfₒ, and is closed below Cnfₒ.

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
successor.  The reverse comparison from the fat successor to the induced
successor is equivalent to excluded middle.  By the general characterization,
the same is true of external mixed transitivity below Cnfₒ.

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

 fat-below-induced-implies-EM : Fat-succ-below-induced → EM 𝓤₀
 fat-below-induced-implies-EM comparison
  = fat-succ-one-⊴-thin-succ-one-implies-EM
     (⊴-trans (fat-succ 𝟙ₒ) (induced-succ 𝟙ₒ) (thin-succ 𝟙ₒ)
       (comparison 𝟙ₒ one-below-base) (below-thin 𝟙ₒ one-below-base))

 EM-implies-fat-below-induced : EM 𝓤₀ → Fat-succ-below-induced
 EM-implies-fat-below-induced em A h
  = transport⁻¹ (fat-succ A ⊴_) (induced-succ-equals-thin A h)
     (EM-implies-fat-succ-⊴-thin-succ em A)

 fat-below-induced-iff-EM : Fat-succ-below-induced ↔ EM 𝓤₀
 fat-below-induced-iff-EM
  = fat-below-induced-implies-EM , EM-implies-fat-below-induced

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

 open Plump
  using (Plumpₒ; is-plump; plump-succ; plump-ordinal-representation)
 open InducedSuccessor (Plumpₒ 𝓤) public

 private
  ＝-⊴-≃ₒ-gives-⊴
   : {A B : Ordinal 𝓥} {C : Ordinal 𝓦} {D : Ordinal 𝓣}
   → A ＝ B → B ⊴ C → C ≃ₒ D → A ⊴ D
  ＝-⊴-≃ₒ-gives-⊴ {A = _} {B} {C} {D} e h f
   = transport⁻¹ (_⊴ D) e (⊴-trans B C D h (≃ₒ-to-⊴ C D f))

  ≃ₒ-⊴-＝-gives-⊴
   : {A : Ordinal 𝓥} {B : Ordinal 𝓦} {C D : Ordinal 𝓣}
   → A ≃ₒ B → B ⊴ C → C ＝ D → A ⊴ D
  ≃ₒ-⊴-＝-gives-⊴ {A = A} {B = B} {C = C} {D = D} e h p
   = ⊴-trans A B D
      (≃ₒ-to-⊴ A B e)
      (⊴-trans B C D h (＝-to-⊴ C D p))

  module Construction
   = Ordinals.OrdinalOfOrdinalsWithProperty.WithProperty ua
      (is-plump {𝓤}) Plump.is-plump-is-prop
      Plump.plump-predecessors-are-plump

\end{code}

The large plump successor of a plump ordinal agrees with the successor induced
at its representing initial segment in the ordinal of plump ordinals.  This
agreement allows us to derive corresponding properties of the plump successor
from those of the induced successor.

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

Consequently, the plump successor of A is weakly below every plump ordinal
strictly above A.

\begin{code}

 plump-succ-relative-leastness
  : (A C : Ordinal 𝓤) → is-plump A → is-plump C
  → A ⊲ C → plump-succ A ⊴ C
 plump-succ-relative-leastness A C p q h = goal
  where
   x y : ⟨ Plumpₒ 𝓤 ⟩
   x = A , p
   y = C , q

   X Y : Ordinal (𝓤 ⁺)
   X = Plumpₒ 𝓤 ↓ x
   Y = Plumpₒ 𝓤 ↓ y

   agreement : plump-succ A ＝ induced-succ X
   agreement = plump-succ-equals-induced-succ A p

   induced-relative-leastness : induced-succ X ⊴ Y
   induced-relative-leastness
    = relative-leastness X Y
       (↓-preserves-order (Plumpₒ 𝓤) x y h) (y , refl)

   representation : C ≃ₒ Y
   representation = plump-ordinal-representation C q

   goal : plump-succ A ⊴ C
   goal
    = ＝-⊴-≃ₒ-gives-⊴ agreement induced-relative-leastness
       (≃ₒ-sym C Y representation)

\end{code}

Under propositional resizing and smallness of weak predecessors, the small
plump successor gives an internal strong and exact successor.  The general
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
     strong-succ-gives-succ (internal-successor x) x (strong-successor x)

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
  closure = has-exact-successors-gives-induced-succ-closure exact-successors

\end{code}

Agreement with the induced successor transfers strict monotonicity to the
plump successor.

\begin{code}

  plump-succ-strict-monotonicity
   : (A C : Ordinal 𝓤)
   → (p : is-plump A) (q : is-plump C)
   → A ⊲ C → plump-succ A ⊲ plump-succ C
  plump-succ-strict-monotonicity A C p q h = goal
   where
    x y : ⟨ Plumpₒ 𝓤 ⟩
    x = A , p
    y = C , q

    X Y : Ordinal (𝓤 ⁺)
    X = Plumpₒ 𝓤 ↓ x
    Y = Plumpₒ 𝓤 ↓ y

    agreement-A : plump-succ A ＝ induced-succ X
    agreement-A = plump-succ-equals-induced-succ A p

    agreement-C : plump-succ C ＝ induced-succ Y
    agreement-C = plump-succ-equals-induced-succ C q

    induced-strict-monotonicity : induced-succ X ⊲ induced-succ Y
    induced-strict-monotonicity
     = strict-monotonicity X Y (x , refl) (y , refl)
        (↓-preserves-order (Plumpₒ 𝓤) x y h)

    goal : plump-succ A ⊲ plump-succ C
    goal
     = transport₂ _⊲_ (agreement-A ⁻¹) (agreement-C ⁻¹)
        induced-strict-monotonicity

\end{code}

The thin successor is weakly below the plump successor, which is weakly below
the fat successor.  The first comparison is transferred from the induced
successor.  The second is the canonical inclusion of the restricted fat
successor into the fat successor.

\begin{code}

 thin-succ-⊴-plump-succ
  : (A : Ordinal 𝓤) (p : is-plump A)
  → thin-succ A ⊴ plump-succ A
 thin-succ-⊴-plump-succ A p = goal
  where
   x : ⟨ Plumpₒ 𝓤 ⟩
   x = A , p

   X : Ordinal (𝓤 ⁺)
   X = Plumpₒ 𝓤 ↓ x

   thin-representation : thin-succ A ≃ₒ thin-succ X
   thin-representation = thin-succ-cong (plump-ordinal-representation A p)

   thin-below-induced : thin-succ X ⊴ induced-succ X
   thin-below-induced = thin-succ-⊴-induced-succ X (x , refl)

   agreement : plump-succ A ＝ induced-succ X
   agreement = plump-succ-equals-induced-succ A p

   goal : thin-succ A ⊴ plump-succ A
   goal
    = ≃ₒ-⊴-＝-gives-⊴ thin-representation thin-below-induced
       (agreement ⁻¹)

 plump-succ-⊴-fat-succ
  : (A : Ordinal 𝓤) → plump-succ A ⊴ fat-succ A
 plump-succ-⊴-fat-succ
  = Construction.restricted-fat-succ-⊴-fat-succ

\end{code}

The weak order on the ordinal of plump ordinals splits exactly when excluded
middle holds.  Hence, the induced successor is weakly below the thin successor
exactly when excluded middle holds.

\begin{code}

 induced-succ-below-thin-iff-EM
  : Induced-succ-below-thin ↔ EM 𝓤
 induced-succ-below-thin-iff-EM
  = ↔-trans induced-succ-⊴-thin-succ-iff-weak-order-splits
     Plump.plump-weak-order-splits-iff-EM

\end{code}

We transfer this characterization to the plump successor using its agreement
with the induced successor.

\begin{code}

 Plump-succ-below-thin : 𝓤 ⁺ ̇
 Plump-succ-below-thin
  = (A : Ordinal 𝓤) → is-plump A → plump-succ A ⊴ thin-succ A

 plump-succ-below-thin-implies-induced-succ-below-thin
  : Plump-succ-below-thin → Induced-succ-below-thin
 plump-succ-below-thin-implies-induced-succ-below-thin
     comparison X ((A , p) , refl) = goal
  where
   agreement : plump-succ A ＝ induced-succ X
   agreement = plump-succ-equals-induced-succ A p

   plump-comparison : plump-succ A ⊴ thin-succ A
   plump-comparison = comparison A p

   thin-representation : thin-succ A ≃ₒ thin-succ X
   thin-representation = thin-succ-cong (plump-ordinal-representation A p)

   goal : induced-succ X ⊴ thin-succ X
   goal
    = ＝-⊴-≃ₒ-gives-⊴ (agreement ⁻¹) plump-comparison
       thin-representation

 induced-succ-below-thin-implies-plump-succ-below-thin
  : Induced-succ-below-thin → Plump-succ-below-thin
 induced-succ-below-thin-implies-plump-succ-below-thin
     comparison A p = goal
  where
   x : ⟨ Plumpₒ 𝓤 ⟩
   x = A , p

   X : Ordinal (𝓤 ⁺)
   X = Plumpₒ 𝓤 ↓ x

   agreement : plump-succ A ＝ induced-succ X
   agreement = plump-succ-equals-induced-succ A p

   induced-comparison : induced-succ X ⊴ thin-succ X
   induced-comparison = comparison X (x , refl)

   thin-representation : thin-succ A ≃ₒ thin-succ X
   thin-representation = thin-succ-cong (plump-ordinal-representation A p)

   goal : plump-succ A ⊴ thin-succ A
   goal
    = ＝-⊴-≃ₒ-gives-⊴ agreement induced-comparison
       (≃ₒ-sym (thin-succ A) (thin-succ X) thin-representation)

 plump-succ-below-thin-iff-induced-succ-below-thin
  : Plump-succ-below-thin ↔ Induced-succ-below-thin
 plump-succ-below-thin-iff-induced-succ-below-thin
  = plump-succ-below-thin-implies-induced-succ-below-thin ,
    induced-succ-below-thin-implies-plump-succ-below-thin

 plump-succ-below-thin-iff-EM
  : Plump-succ-below-thin ↔ EM 𝓤
 plump-succ-below-thin-iff-EM
  = ↔-trans plump-succ-below-thin-iff-induced-succ-below-thin
     induced-succ-below-thin-iff-EM

\end{code}
