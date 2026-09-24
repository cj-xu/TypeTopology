Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg and Chuangjie Xu
23 September 2026

We study the successor operation induced by a base ordinal B.  We establish its
basic order properties and characterize the conditions on B needed for further
properties, such as strict monotonicity.  We also compare the induced successor
with thin and fat successors.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.Univalence

module Ordinals.InducedSuccessor (ua : Univalence) where

open import MLTT.Spartan
open import Ordinals.Equivalence
open import Ordinals.Maps
open import Ordinals.Notions
open import Ordinals.Type
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.Underlying
open import UF.Equiv
open import UF.Subsingletons
open import UF.UA-FunExt using (Univalence-gives-FunExt)

open import Ordinals.AdditionProperties ua
 using (+ₒ-↓-left; successor-lemma-right; successor-increasing)

open import Ordinals.Successors ua

open import Ordinals.LimitPoints (Univalence-gives-FunExt ua)
 using (is-successor-of)

module InducedSuccessor
        {𝓤 : Universe}
        (B : Ordinal 𝓤)
       where

 open Successors B public

 _≺ᴮ_ : ⟨ B ⟩ → ⟨ B ⟩ → 𝓤 ̇
 x ≺ᴮ y = x ≺⟨ B ⟩ y

 _≼ᴮ_ : ⟨ B ⟩ → ⟨ B ⟩ → 𝓤 ̇
 x ≼ᴮ y = x ≼⟨ B ⟩ y

 private
  ≼-gives-↓-⊴ : (x y : ⟨ B ⟩) → x ≼ᴮ y → (B ↓ x) ⊴ (B ↓ y)
  ≼-gives-↓-⊴
   = simulations-pointwise-≼-gives-initial-segments-⊴
      B B B (⊴-refl B) (⊴-refl B)

\end{code}

The successor of A induced by the base ordinal B has as elements the points b
of B whose initial segments B ↓ b are weakly below A, with the order inherited
from B.

\begin{code}

 induced-succ : Ordinal 𝓤 → Ordinal 𝓤
 induced-succ A = X , _≺_ , p , w , e , t
  where
   X : 𝓤 ̇
   X = Σ b ꞉ ⟨ B ⟩ , (B ↓ b) ⊴ A

   _≺_ : X → X → 𝓤 ̇
   (x , _) ≺ (y , _) = x ≺ᴮ y

   p : is-prop-valued _≺_
   p (x , _) (y , _) = Prop-valuedness B x y

   w : is-well-founded _≺_
   w (x , h) = f x (Well-foundedness B x) h
    where
     f : (x : ⟨ B ⟩)
       → is-accessible _≺ᴮ_ x
       → (h : (B ↓ x) ⊴ A) → is-accessible _≺_ (x , h)
     f x (acc s) h
      = acc (λ σ l → f (pr₁ σ) (s (pr₁ σ) l) (pr₂ σ))

   below : (x y : ⟨ B ⟩)
         → x ≺ᴮ y → (B ↓ y) ⊴ A → (B ↓ x) ⊴ A
   below x y l h
    = ⊴-trans (B ↓ x) (B ↓ y) A
     (⊲-gives-⊴ (B ↓ x) (B ↓ y) (↓-preserves-order B x y l)) h

   e : is-extensional _≺_
   e (x , h) (y , k) f g
    = to-subtype-＝
     (λ b → ⊴-is-prop-valued (B ↓ b) A)
     (Extensionality B x y
       (λ z l → f (z , below z x l h) l)
       (λ z l → g (z , below z y l k) l))

   t : is-transitive _≺_
   t (x , _) (y , _) (z , _) = Transitivity B x y z

\end{code}

We first present the properties of induced-succ for arbitrary input ordinals,
without assuming that they lie strictly below B.

■ Bounds and the induced successor of the base

Every induced successor is weakly below B.  At B itself, the reverse
comparison also holds, so induced-succ B equals B.

\begin{code}

 induced-succ-⊴-base : (A : Ordinal 𝓤) → induced-succ A ⊴ B
 induced-succ-⊴-base A = pr₁ , i , p
  where
   i : is-initial-segment (induced-succ A) B pr₁
   i (x , h) y l = (y , k) , l , refl
    where
     k : (B ↓ y) ⊴ A
     k = ⊴-trans (B ↓ y) (B ↓ x) A
          (⊲-gives-⊴ (B ↓ y) (B ↓ x) (↓-preserves-order B y x l)) h

   p : is-order-preserving (induced-succ A) B pr₁
   p (x , _) (y , _) l = l

\end{code}

The initial segment of induced-succ A at (b , h) is the initial segment
of B at b.  This identity relates predecessors of induced-succ A to those
of B.

\begin{code}

 induced-succ-initial-segment
  : (A : Ordinal 𝓤) (b : ⟨ B ⟩) (h : (B ↓ b) ⊴ A)
  → induced-succ A ↓ (b , h) ＝ B ↓ b
 induced-succ-initial-segment A b h
  = simulations-preserve-↓ (induced-succ A) B (induced-succ-⊴-base A)
     (b , h)

\end{code}

The base ordinal is weakly below its own induced successor.

\begin{code}

 base-⊴-induced-succ-base : B ⊴ induced-succ B
 base-⊴-induced-succ-base = f , i , p
  where
   f : ⟨ B ⟩ → ⟨ induced-succ B ⟩
   f b = b , segment-⊴ B b

   i : is-initial-segment B (induced-succ B) f
   i x (y , h) l
    = y , l , to-subtype-＝ (λ b → ⊴-is-prop-valued (B ↓ b) B) refl

   p : is-order-preserving B (induced-succ B) f
   p x y l = l

\end{code}

The two bounds give equality at the base ordinal.

\begin{code}

 induced-succ-base : induced-succ B ＝ B
 induced-succ-base
  = ⊴-antisym (induced-succ B) B
     (induced-succ-⊴-base B) base-⊴-induced-succ-base

\end{code}

■ The induced successor is monotone with respect to the weak order ⊴.

\begin{code}

 induced-succ-monotone-⊴ : (A C : Ordinal 𝓤)
                         → A ⊴ C → induced-succ A ⊴ induced-succ C
 induced-succ-monotone-⊴ A C h = f , i , p
  where
   f : ⟨ induced-succ A ⟩ → ⟨ induced-succ C ⟩
   f (x , k) = x , ⊴-trans (B ↓ x) A C k h

   i : is-initial-segment (induced-succ A) (induced-succ C) f
   i (x , k) (y , l) m
    = (y , n) , m , to-subtype-＝ (λ b → ⊴-is-prop-valued (B ↓ b) C) refl
    where
     n : (B ↓ y) ⊴ A
     n = ⊴-trans (B ↓ y) (B ↓ x) A
          (⊲-gives-⊴ (B ↓ y) (B ↓ x) (↓-preserves-order B y x m)) k

   p : is-order-preserving (induced-succ A) (induced-succ C) f
   p (x , _) (y , _) l = l

\end{code}

■ Every ordinal strictly below the induced successor of A is weakly below A.

\begin{code}

 ⊲-induced-succ-gives-⊴ : (A C : Ordinal 𝓤) → C ⊲ induced-succ A → C ⊴ A
 ⊲-induced-succ-gives-⊴ A C ((b , h) , e)
  = ⊴-trans C (B ↓ b) A (＝-to-⊴ C (B ↓ b) (e ∙ q)) h
  where
   q : induced-succ A ↓ (b , h) ＝ B ↓ b
   q = induced-succ-initial-segment A b h

\end{code}

We now relate the predecessors of induced-succ A to the ordinals strictly
below B, and then study induced-succ on inputs strictly below B.

■ For C strictly below B, C ⊲ induced-succ A iff C ⊴ A.

Here A may be arbitrary; only C is required to be strictly below B.

\begin{code}

 ⊴-gives-⊲-induced-succ : (A C : Ordinal 𝓤) → C ⊲ B
                        → C ⊴ A → C ⊲ induced-succ A
 ⊴-gives-⊲-induced-succ A C (b , refl) h = (b , h) , (q ⁻¹)
  where
   q : induced-succ A ↓ (b , h) ＝ B ↓ b
   q = induced-succ-initial-segment A b h

 ⊲-induced-succ-iff-⊴ : (A C : Ordinal 𝓤) → C ⊲ B
                      → (C ⊲ induced-succ A ↔ C ⊴ A)
 ⊲-induced-succ-iff-⊴ A C h
  = ⊲-induced-succ-gives-⊴ A C , ⊴-gives-⊲-induced-succ A C h

\end{code}

■ Every ordinal strictly below B is strictly below its induced successor.

\begin{code}

 ⊲-induced-succ : (A : Ordinal 𝓤) → A ⊲ B → A ⊲ induced-succ A
 ⊲-induced-succ A h = ⊴-gives-⊲-induced-succ A A h (⊴-refl A)

\end{code}

■ Order reflection and injectivity below B

The induced successor reflects ⊴ when its source is strictly below B.

\begin{code}

 induced-succ-reflects-⊴ : (A C : Ordinal 𝓤) → A ⊲ B
                         → induced-succ A ⊴ induced-succ C → A ⊴ C
 induced-succ-reflects-⊴ A C h k
  = ⊲-induced-succ-gives-⊴ C A
     (⊲-⊴-gives-⊲ A (induced-succ A) (induced-succ C) (⊲-induced-succ A h) k)

\end{code}

It also reflects ⊲ under the same assumption.

\begin{code}

 induced-succ-reflects-⊲ : (A C : Ordinal 𝓤) → A ⊲ B
                         → induced-succ A ⊲ induced-succ C → A ⊲ C
 induced-succ-reflects-⊲ A C h k
  = ⊲-⊴-gives-⊲ A (induced-succ A) C (⊲-induced-succ A h)
     (⊲-induced-succ-gives-⊴ C (induced-succ A) k)

\end{code}

Reflection of ⊴ gives injectivity on ordinals strictly below B.

\begin{code}

 induced-succ-injective : (A C : Ordinal 𝓤) → A ⊲ B → C ⊲ B
                        → induced-succ A ＝ induced-succ C → A ＝ C
 induced-succ-injective A C h k e = ⊴-antisym A C f g
  where
   f : A ⊴ C
   f = induced-succ-reflects-⊴ A C h
        (＝-to-⊴ (induced-succ A) (induced-succ C) e)

   g : C ⊴ A
   g = induced-succ-reflects-⊴ C A k
        (＝-to-⊴ (induced-succ C) (induced-succ A) (e ⁻¹))

\end{code}

The above properties hold for an arbitrary base ordinal B.  We now characterize
four further expected properties of induced-succ in terms of additional
conditions on B: leastness relative to ordinals strictly below B, commutation
with a given internal strong successor on B, strict monotonicity below B, and
closure of the ordinals strictly below B under induced-succ.

■ Leastness relative to ordinals strictly below B

Relative leastness means that induced-succ A is weakly below every strict upper
bound of A that is itself strictly below B.  We characterize this property by
mixed transitivity on B: x ≼ᴮ y and y ≺ᴮ z imply x ≺ᴮ z.

\begin{code}

 Induced-succ-relative-leastness : 𝓤 ⁺ ̇
 Induced-succ-relative-leastness
  = (A C : Ordinal 𝓤) → A ⊲ C → C ⊲ B → induced-succ A ⊴ C

 Mixed-transitivity : 𝓤 ̇
 Mixed-transitivity = (x y z : ⟨ B ⟩) → x ≼ᴮ y → y ≺ᴮ z → x ≺ᴮ z

\end{code}

Relative leastness implies mixed transitivity by applying it to initial segments
of B.  Conversely, mixed transitivity makes the first projection from
induced-succ A into any initial segment of B strictly above A a simulation.

\begin{code}

 induced-succ-relative-leastness-gives-mixed-transitivity
  : Induced-succ-relative-leastness → Mixed-transitivity
 induced-succ-relative-leastness-gives-mixed-transitivity least x y z h k
  = transport (λ b → b ≺ᴮ z) q (pr₂ (pr₁ m (x , h')))
  where
   h' : (B ↓ x) ⊴ (B ↓ y)
   h' = ≼-gives-↓-⊴ x y h

   m : induced-succ (B ↓ y) ⊴ (B ↓ z)
   m = least (B ↓ y) (B ↓ z) (↓-preserves-order B y z k) (z , refl)

   q : pr₁ (pr₁ m (x , h')) ＝ x
   q = ap (λ s → pr₁ s (x , h'))
        (⊴-is-prop-valued (induced-succ (B ↓ y)) B
          (⊴-trans (induced-succ (B ↓ y)) (B ↓ z) B m (segment-⊴ B z))
          (induced-succ-⊴-base (B ↓ y)))

 mixed-transitivity-gives-induced-succ-relative-leastness
  : Mixed-transitivity → Induced-succ-relative-leastness
 mixed-transitivity-gives-induced-succ-relative-leastness
  mixed A C h (c , refl) = f , i , p
  where
   a : ⟨ B ⟩
   a = pr₁ (⊲-witness h)

   l : a ≺ᴮ c
   l = pr₂ (⊲-witness h)

   abstract
    q : A ＝ B ↓ a
    q = ⊲-witness-property h ∙ iterated-↓ B c a l

    below : (x : ⟨ B ⟩) → (B ↓ x) ⊴ A → x ≺ᴮ c
    below x h
     = mixed x a c
        (↓-⊴-lc B x a
          (⊴-trans (B ↓ x) A (B ↓ a) h (＝-to-⊴ A (B ↓ a) q))) l

   f : ⟨ induced-succ A ⟩ → ⟨ B ↓ c ⟩
   f (x , h) = x , below x h

   i : is-initial-segment (induced-succ A) (B ↓ c) f
   i (x , h) (y , k) m
    = (y , n) , m , to-subtype-＝ (λ b → Prop-valuedness B b c) refl
    where
     n : (B ↓ y) ⊴ A
     n = ⊴-trans (B ↓ y) (B ↓ x) A
          (⊲-gives-⊴ (B ↓ y) (B ↓ x) (↓-preserves-order B y x m)) h

   p : is-order-preserving (induced-succ A) (B ↓ c) f
   p (x , _) (y , _) m = m

 induced-succ-relative-leastness-iff-mixed-transitivity
  : Induced-succ-relative-leastness ↔ Mixed-transitivity
 induced-succ-relative-leastness-iff-mixed-transitivity
  = induced-succ-relative-leastness-gives-mixed-transitivity ,
    mixed-transitivity-gives-induced-succ-relative-leastness

\end{code}

■ Commutation with a given internal strong successor on B

Given an internal strong successor s on B, we ask whether taking initial
segments carries s to induced-succ: for every x in B, the initial segment
B ↓ (s x) should equal induced-succ (B ↓ x).

\begin{code}

 Induced-succ-commutes-with : (⟨ B ⟩ → ⟨ B ⟩) → 𝓤 ⁺ ̇
 Induced-succ-commutes-with s = (x : ⟨ B ⟩) → B ↓ (s x) ＝ induced-succ (B ↓ x)

\end{code}

For a given internal strong successor s, this commutation property is also
equivalent to mixed transitivity on B.

\begin{code}

 induced-succ-commutation-gives-mixed-transitivity
  : (s : ⟨ B ⟩ → ⟨ B ⟩) → calc-strong-succ s
  → Induced-succ-commutes-with s → Mixed-transitivity
 induced-succ-commutation-gives-mixed-transitivity s strong commutes
  x y z h k = pr₂ (pr₂ (strong y)) z k x below
  where
   u : ⟨ induced-succ (B ↓ y) ⟩
   u = x , ≼-gives-↓-⊴ x y h

   m : induced-succ (B ↓ y) ⊴ (B ↓ s y)
   m = ＝-to-⊴ (induced-succ (B ↓ y)) (B ↓ s y) (commutes y ⁻¹)

   q : pr₁ (pr₁ m u) ＝ x
   q = ap (λ t → pr₁ t u)
        (⊴-is-prop-valued (induced-succ (B ↓ y)) B
          (⊴-trans (induced-succ (B ↓ y)) (B ↓ s y) B m (segment-⊴ B (s y)))
          (induced-succ-⊴-base (B ↓ y)))

   below : x ≺ᴮ s y
   below = transport (λ b → b ≺ᴮ s y) q (pr₂ (pr₁ m u))

 mixed-transitivity-gives-induced-succ-commutation
  : (s : ⟨ B ⟩ → ⟨ B ⟩) → calc-strong-succ s
  → Mixed-transitivity → Induced-succ-commutes-with s
 mixed-transitivity-gives-induced-succ-commutation s strong mixed x
  = ⊴-antisym (B ↓ s x) (induced-succ (B ↓ x)) lower upper
  where
   abstract
    predecessor : (y : ⟨ B ⟩) → y ≺ᴮ s x → (B ↓ y) ⊴ (B ↓ x)
    predecessor y h = ≼-gives-↓-⊴ y x (pr₁ (pr₂ (strong x)) y h)

   f : ⟨ B ↓ s x ⟩ → ⟨ induced-succ (B ↓ x) ⟩
   f (y , h) = y , predecessor y h

   i : is-initial-segment (B ↓ s x) (induced-succ (B ↓ x)) f
   i (y , h) (z , k) l
    = (z , Transitivity B z y (s x) l h) , l ,
      to-subtype-＝ (λ b → ⊴-is-prop-valued (B ↓ b) (B ↓ x)) refl

   p : is-order-preserving (B ↓ s x) (induced-succ (B ↓ x)) f
   p (y , _) (z , _) l = l

   lower : (B ↓ s x) ⊴ induced-succ (B ↓ x)
   lower = f , i , p

   upper : induced-succ (B ↓ x) ⊴ (B ↓ s x)
   upper = mixed-transitivity-gives-induced-succ-relative-leastness mixed
            (B ↓ x) (B ↓ s x)
            (↓-preserves-order B x (s x) (pr₁ (strong x))) (s x , refl)

 induced-succ-commutation-iff-mixed-transitivity
  : (s : ⟨ B ⟩ → ⟨ B ⟩) → calc-strong-succ s
  → (Induced-succ-commutes-with s ↔ Mixed-transitivity)
 induced-succ-commutation-iff-mixed-transitivity s strong
  = induced-succ-commutation-gives-mixed-transitivity s strong ,
    mixed-transitivity-gives-induced-succ-commutation s strong

\end{code}

■ Strict monotonicity below B

Strict monotonicity of induced-succ below B implies relative leastness, and
hence mixed transitivity of B.

\begin{code}

 Induced-succ-strict-monotonicity : 𝓤 ⁺ ̇
 Induced-succ-strict-monotonicity
  = (A C : Ordinal 𝓤) → A ⊲ B → C ⊲ B
  → A ⊲ C → induced-succ A ⊲ induced-succ C

 induced-succ-strict-monotonicity-gives-mixed-transitivity
  : Induced-succ-strict-monotonicity → Mixed-transitivity
 induced-succ-strict-monotonicity-gives-mixed-transitivity monotone
  = induced-succ-relative-leastness-gives-mixed-transitivity least
  where
   least : Induced-succ-relative-leastness
   least A C h k
    = ⊲-induced-succ-gives-⊴ C (induced-succ A)
       (monotone A C (⊲-is-transitive A C B h k) k h)

\end{code}

For the converse, we additionally require that every element with a strict upper
bound in B has a successor.  Together with mixed transitivity, this condition
characterizes strict monotonicity of induced-succ below B.  Here "bounded" means
having a strict upper bound in B.

\begin{code}

 has-a-succ : ⟨ B ⟩ → 𝓤 ̇
 has-a-succ x = Σ s ꞉ ⟨ B ⟩ , is-successor-of B s x

 Bounded-elements-have-successors : 𝓤 ̇
 Bounded-elements-have-successors = (x y : ⟨ B ⟩) → x ≺ᴮ y → has-a-succ x

\end{code}

Strict monotonicity makes induced-succ (B ↓ x) an initial segment of B whenever
x has a strict upper bound.  Its representing element is a successor of x.

\begin{code}

 induced-succ-strict-monotonicity-gives-bounded-elements-have-successors
  : Induced-succ-strict-monotonicity → Bounded-elements-have-successors
 induced-succ-strict-monotonicity-gives-bounded-elements-have-successors
  monotone x y h = s , below , predecessor
  where
   represented : induced-succ (B ↓ x) ⊲ B
   represented
    = ⊲-⊴-gives-⊲ (induced-succ (B ↓ x)) (induced-succ (B ↓ y)) B
       (monotone (B ↓ x) (B ↓ y) (x , refl) (y , refl)
         (↓-preserves-order B x y h))
       (induced-succ-⊴-base (B ↓ y))

   s : ⟨ B ⟩
   s = ⊲-witness represented

   q : induced-succ (B ↓ x) ＝ B ↓ s
   q = ⊲-witness-property represented

   below : x ≺ᴮ s
   below = ↓-reflects-order B x s
            (transport (λ A → (B ↓ x) ⊲ A) q
              (⊲-induced-succ (B ↓ x) (x , refl)))

   predecessor : (z : ⟨ B ⟩) → z ≺ᴮ s → z ≼ᴮ x
   predecessor z k
    = ↓-⊴-lc B z x
       (⊲-induced-succ-gives-⊴ (B ↓ x) (B ↓ z)
         (transport⁻¹ (λ A → (B ↓ z) ⊲ A) q
           (↓-preserves-order B z s k)))

\end{code}

Conversely, mixed transitivity and successors for bounded elements make
induced-succ strictly monotone below B.  Together, these two conditions
therefore characterize strict monotonicity below B.

\begin{code}

 mixed-transitivity-and-bounded-successors-give-strict-monotonicity
  : Mixed-transitivity × Bounded-elements-have-successors
  → Induced-succ-strict-monotonicity
 mixed-transitivity-and-bounded-successors-give-strict-monotonicity
  (mixed , successors) A C (a , refl) (c , refl) h
   = ⊴-gives-⊲-induced-succ (B ↓ c) (induced-succ (B ↓ a))
      (s , q) (least (B ↓ a) (B ↓ c) h (c , refl))
  where
   least : Induced-succ-relative-leastness
   least = mixed-transitivity-gives-induced-succ-relative-leastness mixed

   witness : has-a-succ a
   witness = successors a c (↓-reflects-order B a c h)

   s : ⟨ B ⟩
   s = pr₁ witness

   a-below-s : a ≺ᴮ s
   a-below-s = pr₁ (pr₂ witness)

   predecessor : (z : ⟨ B ⟩) → z ≺ᴮ s → z ≼ᴮ a
   predecessor = pr₂ (pr₂ witness)

   f : ⟨ B ↓ s ⟩ → ⟨ induced-succ (B ↓ a) ⟩
   f (z , k) = z , ≼-gives-↓-⊴ z a (predecessor z k)

   i : is-initial-segment (B ↓ s) (induced-succ (B ↓ a)) f
   i (z , k) (w , l) m
    = (w , Transitivity B w z s m k) , m ,
      to-subtype-＝ (λ b → ⊴-is-prop-valued (B ↓ b) (B ↓ a)) refl

   p : is-order-preserving (B ↓ s) (induced-succ (B ↓ a)) f
   p (z , _) (w , _) k = k

   q : induced-succ (B ↓ a) ＝ B ↓ s
   q = ⊴-antisym (induced-succ (B ↓ a)) (B ↓ s)
        (least (B ↓ a) (B ↓ s) (↓-preserves-order B a s a-below-s)
          (s , refl))
        (f , i , p)

 induced-succ-strict-monotonicity-iff-mixed-transitivity-and-bounded-successors
  : Induced-succ-strict-monotonicity
  ↔ (Mixed-transitivity × Bounded-elements-have-successors)
 induced-succ-strict-monotonicity-iff-mixed-transitivity-and-bounded-successors
  = (λ monotone →
      induced-succ-strict-monotonicity-gives-mixed-transitivity monotone ,
      induced-succ-strict-monotonicity-gives-bounded-elements-have-successors
       monotone) ,
    mixed-transitivity-and-bounded-successors-give-strict-monotonicity

\end{code}

■ Closure under induced-succ

Closure means that induced-succ A remains strictly below B whenever A is
strictly below B.  Thus induced-succ acts on the ordinals strictly below B and
can be iterated there.

\begin{code}

 Induced-succ-closure : 𝓤 ⁺ ̇
 Induced-succ-closure = (A : Ordinal 𝓤) → A ⊲ B → induced-succ A ⊲ B

\end{code}

Closure under induced-succ is characterized by the existence of an exact
successor for every element of B.

A point representing induced-succ (B ↓ x) is an exact successor of x;
conversely, an exact successor of x represents induced-succ (B ↓ x).

\begin{code}

 induced-succ-closure-gives-has-exact-successors
  : Induced-succ-closure → Has-exact-successors
 induced-succ-closure-gives-has-exact-successors closed x = s , exact
  where
   represented : induced-succ (B ↓ x) ⊲ B
   represented = closed (B ↓ x) (x , refl)

   s : ⟨ B ⟩
   s = ⊲-witness represented

   q : induced-succ (B ↓ x) ＝ B ↓ s
   q = ⊲-witness-property represented

   exact : s is-exact-succ-of x
   exact z = forward , backward
    where
     forward : z ≺ᴮ s → z ≼ᴮ x
     forward h
      = ↓-⊴-lc B z x
         (⊲-induced-succ-gives-⊴ (B ↓ x) (B ↓ z)
           (transport⁻¹ (λ A → (B ↓ z) ⊲ A) q
             (↓-preserves-order B z s h)))

     backward : z ≼ᴮ x → z ≺ᴮ s
     backward h
      = ↓-reflects-order B z s
         (transport (λ A → (B ↓ z) ⊲ A) q
           (⊴-gives-⊲-induced-succ (B ↓ x) (B ↓ z) (z , refl)
             (≼-gives-↓-⊴ z x h)))

 has-exact-successors-gives-induced-succ-closure
  : Has-exact-successors → Induced-succ-closure
 has-exact-successors-gives-induced-succ-closure successors A (x , refl)
  = s , ⊴-antisym (induced-succ (B ↓ x)) (B ↓ s) (f , i , p) (g , j , r)
  where
   s : ⟨ B ⟩
   s = pr₁ (successors x)

   exact : s is-exact-succ-of x
   exact = pr₂ (successors x)

   f : ⟨ induced-succ (B ↓ x) ⟩ → ⟨ B ↓ s ⟩
   f (z , h) = z , pr₂ (exact z) (↓-⊴-lc B z x h)

   i : is-initial-segment (induced-succ (B ↓ x)) (B ↓ s) f
   i (z , h) (w , k) l
    = (w , n) , l , to-subtype-＝ (λ b → Prop-valuedness B b s) refl
    where
     n : (B ↓ w) ⊴ (B ↓ x)
     n = ⊴-trans (B ↓ w) (B ↓ z) (B ↓ x)
          (⊲-gives-⊴ (B ↓ w) (B ↓ z) (↓-preserves-order B w z l)) h

   p : is-order-preserving (induced-succ (B ↓ x)) (B ↓ s) f
   p (z , _) (w , _) h = h

   g : ⟨ B ↓ s ⟩ → ⟨ induced-succ (B ↓ x) ⟩
   g (z , h) = z , ≼-gives-↓-⊴ z x (pr₁ (exact z) h)

   j : is-initial-segment (B ↓ s) (induced-succ (B ↓ x)) g
   j (z , h) (w , k) l
    = (w , Transitivity B w z s l h) , l ,
      to-subtype-＝ (λ b → ⊴-is-prop-valued (B ↓ b) (B ↓ x)) refl

   r : is-order-preserving (B ↓ s) (induced-succ (B ↓ x)) g
   r (z , _) (w , _) h = h

 induced-succ-closure-iff-has-exact-successors
  : Induced-succ-closure ↔ Has-exact-successors
 induced-succ-closure-iff-has-exact-successors
  = induced-succ-closure-gives-has-exact-successors ,
    has-exact-successors-gives-induced-succ-closure

\end{code}

■ Comparison with thin and fat successors

For every A strictly below B, the thin successor is weakly below the induced
successor, which is weakly below the fat successor.  The latter comparison
holds for arbitrary A.

\begin{code}

 thin-succ-⊴-induced-succ : (A : Ordinal 𝓤) → A ⊲ B
                          → thin-succ A ⊴ induced-succ A
 thin-succ-⊴-induced-succ A h
  = ≼-gives-⊴ (thin-succ A) (induced-succ A)
     (pr₂ (pr₂ (thin-succ-is-strong-succ A))
       (induced-succ A) (⊲-induced-succ A h))

 induced-succ-⊴-fat-succ : (A : Ordinal 𝓤)
                         → induced-succ A ⊴ fat-succ A
 induced-succ-⊴-fat-succ A = f , i , p
  where
   f : ⟨ induced-succ A ⟩ → ⟨ fat-succ A ⟩
   f (b , h) = (B ↓ b) , h

   i : is-initial-segment (induced-succ A) (fat-succ A) f
   i (b , h) (C , k) ((c , l) , e)
    = (c , transport (λ D → D ⊴ A) q k) , l ,
      to-subtype-＝ (λ D → ⊴-is-prop-valued D A) (q ⁻¹)
    where
     q : C ＝ B ↓ c
     q = e ∙ iterated-↓ B b c l

   p : is-order-preserving (induced-succ A) (fat-succ A) f
   p (b , _) (c , _) h = ↓-preserves-order B b c h

\end{code}

However, the converse comparisons need not hold constructively.

■ The reverse comparison with the thin successor

The weak order on B splits if x ≼ᴮ y implies x ≺ᴮ y or x ＝ y.  This condition
characterizes induced-succ A ⊴ thin-succ A for every A strictly below B.

\begin{code}

 Induced-succ-below-thin : 𝓤 ⁺ ̇
 Induced-succ-below-thin
  = (A : Ordinal 𝓤) → A ⊲ B → induced-succ A ⊴ thin-succ A

 Weak-order-splits : 𝓤 ̇
 Weak-order-splits = (x y : ⟨ B ⟩) → x ≼ᴮ y → (x ≺ᴮ y) + (x ＝ y)

 induced-succ-⊴-thin-succ-gives-weak-order-splits
  : Induced-succ-below-thin → Weak-order-splits
 induced-succ-⊴-thin-succ-gives-weak-order-splits comparison x y h
  = split (pr₁ m u) refl
  where
   A = B ↓ y

   u : ⟨ induced-succ A ⟩
   u = x , ≼-gives-↓-⊴ x y h

   m : induced-succ A ⊴ thin-succ A
   m = comparison A (y , refl)

   q : B ↓ x ＝ thin-succ A ↓ pr₁ m u
   q = (induced-succ-initial-segment A x (pr₂ u)) ⁻¹
       ∙ simulations-preserve-↓ (induced-succ A) (thin-succ A) m u

   split : (t : ⟨ thin-succ A ⟩) → pr₁ m u ＝ t
         → (x ≺ᴮ y) + (x ＝ y)
   split (inl (z , l)) e = inl (transport⁻¹ (_≺ᴮ y) r l)
    where
     r : x ＝ z
     r = ↓-lc B x z
          (q ∙ ap (thin-succ A ↓_) e
             ∙ (+ₒ-↓-left (z , l)) ⁻¹ ∙ iterated-↓ B y z l)
   split (inr ⋆) e
    = inr (↓-lc B x y
            (q ∙ ap (thin-succ A ↓_) e ∙ successor-lemma-right A))

 weak-order-splits-gives-induced-succ-⊴-thin-succ
  : Weak-order-splits → Induced-succ-below-thin
 weak-order-splits-gives-induced-succ-⊴-thin-succ splits A (y , refl)
  = to-⊴ (induced-succ (B ↓ y)) (thin-succ (B ↓ y)) below
  where
   below : (u : ⟨ induced-succ (B ↓ y) ⟩)
         → (induced-succ (B ↓ y) ↓ u) ⊲ thin-succ (B ↓ y)
   below (x , h)
    = transport⁻¹ (_⊲ thin-succ (B ↓ y)) q
       (split (splits x y (↓-⊴-lc B x y h)))
    where
     q : induced-succ (B ↓ y) ↓ (x , h) ＝ B ↓ x
     q = induced-succ-initial-segment (B ↓ y) x h

     split : (x ≺ᴮ y) + (x ＝ y) → (B ↓ x) ⊲ thin-succ (B ↓ y)
     split (inl l)
      = ⊲-is-transitive (B ↓ x) (B ↓ y) (thin-succ (B ↓ y))
         (↓-preserves-order B x y l) (successor-increasing (B ↓ y))
     split (inr e)
      = transport⁻¹ (λ z → (B ↓ z) ⊲ thin-succ (B ↓ y)) e
         (successor-increasing (B ↓ y))

 induced-succ-⊴-thin-succ-iff-weak-order-splits
  : Induced-succ-below-thin ↔ Weak-order-splits
 induced-succ-⊴-thin-succ-iff-weak-order-splits
  = induced-succ-⊴-thin-succ-gives-weak-order-splits ,
    weak-order-splits-gives-induced-succ-⊴-thin-succ

\end{code}

■ The reverse comparison with the fat successor

The comparison fat-succ A ⊴ induced-succ A for every A strictly below B is
characterized by external mixed transitivity below B: if C ⊴ A and A ⊲ B,
then C ⊲ B.  Here A and C lie in the same universe as B.

Unlike Mixed-transitivity, this condition concerns ordinal comparison, rather
than the order on points of B.

\begin{code}

 Fat-succ-below-induced : 𝓤 ⁺ ̇
 Fat-succ-below-induced
  = (A : Ordinal 𝓤) → A ⊲ B → fat-succ A ⊴ induced-succ A

 External-mixed-transitivity-below-base : 𝓤 ⁺ ̇
 External-mixed-transitivity-below-base
  = (A C : Ordinal 𝓤) → C ⊴ A → A ⊲ B → C ⊲ B

\end{code}

The reverse comparison represents every ordinal weakly below A as an initial
segment of B.  Conversely, external mixed transitivity makes the canonical
simulation from induced-succ A to fat-succ A an equivalence.

\begin{code}

 fat-succ-⊴-induced-succ-gives-external-mixed-transitivity-below-base
  : Fat-succ-below-induced → External-mixed-transitivity-below-base
 fat-succ-⊴-induced-succ-gives-external-mixed-transitivity-below-base
  comparison A C h below
   = ⌜ ⊲-is-equivalent-to-⊲⁻ C B ⌝⁻¹ (b , e)
  where
   m : fat-succ A ⊴ B
   m = ⊴-trans (fat-succ A) (induced-succ A) B
        (comparison A below) (induced-succ-⊴-base A)

   b : ⟨ B ⟩
   b = pr₁ m (C , h)

   e : C ≃ₒ (B ↓ b)
   e = ≃ₒ-trans C (fat-succ A ↓ (C , h)) (B ↓ b)
        (fat-succ-initial-segment A C h)
        (simulations-pointwise-equal-gives-isomorphic-initial-segments
          (fat-succ A) B B m (⊴-refl B) (C , h) b refl)

 external-mixed-transitivity-below-base-gives-fat-succ-⊴-induced-succ
  : External-mixed-transitivity-below-base → Fat-succ-below-induced
 external-mixed-transitivity-below-base-gives-fat-succ-⊴-induced-succ
  mixed A below
   = ≃ₒ-to-⊴ (fat-succ A) (induced-succ A)
      (≃ₒ-sym (induced-succ A) (fat-succ A) (f , pr₂ sim , e , r))
  where
   f : ⟨ induced-succ A ⟩ → ⟨ fat-succ A ⟩
   f = pr₁ (induced-succ-⊴-fat-succ A)

   sim : is-simulation (induced-succ A) (fat-succ A) f
   sim = pr₂ (induced-succ-⊴-fat-succ A)

   section : (v : ⟨ fat-succ A ⟩)
           → Σ u ꞉ ⟨ induced-succ A ⟩ , f u ＝ v
   section (C , h)
    = (b , transport (_⊴ A) q h) ,
      to-subtype-＝ (λ D → ⊴-is-prop-valued D A) (q ⁻¹)
    where
     represented : C ⊲ B
     represented = mixed A C h below

     b : ⟨ B ⟩
     b = ⊲-witness represented

     q : C ＝ B ↓ b
     q = ⊲-witness-property represented

   e : is-equiv f
   e = lc-split-surjections-are-equivs f
        (simulations-are-lc (induced-succ A) (fat-succ A) f sim) section

   r : is-order-preserving (fat-succ A) (induced-succ A) (inverse f e)
   r = order-reflecting-gives-inverse-order-preserving
        (induced-succ A) (fat-succ A) f e
        (simulations-are-order-reflecting (induced-succ A) (fat-succ A) f sim)

 fat-succ-⊴-induced-succ-iff-external-mixed-transitivity-below-base
  : Fat-succ-below-induced ↔ External-mixed-transitivity-below-base
 fat-succ-⊴-induced-succ-iff-external-mixed-transitivity-below-base
  = fat-succ-⊴-induced-succ-gives-external-mixed-transitivity-below-base ,
    external-mixed-transitivity-below-base-gives-fat-succ-⊴-induced-succ

\end{code}
