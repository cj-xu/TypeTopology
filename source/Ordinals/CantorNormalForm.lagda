Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg and Chuangjie Xu
24 September 2026

We port a minimal fragment of the Cantor normal form formalization from
"Three Equivalent Ordinal Notation Systems in Cubical Agda" by Fredrik
Nordvall Forsberg, Chuangjie Xu, and Neil Ghani (CPP 2020) into TypeTopology.
Our aim is to study the ordinal successor operation induced by the ordinal
of Cantor normal forms.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Ordinals.CantorNormalForm where

open import MLTT.Spartan hiding (succ)
import Ordinals.Notions
open import Ordinals.Type using (Ordinal)
open import UF.DiscreteAndSeparated
open import UF.Sets
open import UF.Base
open import UF.Subsingletons

\end{code}

■ Syntax and order

A nonzero normal form has the shape ω^ a + b.  The side condition
exponent b ≦ a ensures that the leading exponent of b does not exceed a.
We set exponent 𝟎 = 𝟎, so the condition also permits a zero remainder.

The strict order is lexicographic: zero is below every nonzero normal form;
otherwise we compare the leading exponents, then the remainders when the
exponents are equal.  These definitions are mutual because the syntax
contains an order witness and the order is defined on the syntax.

\begin{code}

infix 4 _<_ _≦_

mutual

 data Cnf : 𝓤₀ ̇ where
  𝟎 : Cnf
  ω^_+_[_] : (a b : Cnf) → exponent b ≦ a → Cnf

 data _<_ : Cnf → Cnf → 𝓤₀ ̇ where
  <₁ : ∀ {a b r} → 𝟎 < ω^ a + b [ r ]
  <₂ : ∀ {a b c d r s} → a < b
     → ω^ a + c [ r ] < ω^ b + d [ s ]
  <₃ : ∀ {a b c d r s} → a ＝ b → c < d
     → ω^ a + c [ r ] < ω^ b + d [ s ]

 exponent : Cnf → Cnf
 exponent 𝟎 = 𝟎
 exponent (ω^ a + b [ r ]) = a

 _≦_ : Cnf → Cnf → 𝓤₀ ̇
 a ≦ b = Ordinals.Notions._≦_ _<_ a b

open Ordinals.Notions _<_ hiding (_≦_) renaming (extensional-po to _≼_)

remainder : Cnf → Cnf
remainder 𝟎 = 𝟎
remainder (ω^ a + b [ r ]) = b

𝟎-is-not-ω^+ : {a b : Cnf} {r : exponent b ≦ a} → 𝟎 ≠ ω^ a + b [ r ]
𝟎-is-not-ω^+ ()

ω^+-is-not-𝟎 : {a b : Cnf} {r : exponent b ≦ a} → ω^ a + b [ r ] ≠ 𝟎
ω^+-is-not-𝟎 ()

\end{code}

■ The order is irreflexive and transitive.

Irreflexivity and transitivity follow recursively from the lexicographic order.

\begin{code}

<-is-irreflexive : is-irreflexive
<-is-irreflexive 𝟎 ()
<-is-irreflexive (ω^ a + b [ r ]) (<₂ h) = <-is-irreflexive a h
<-is-irreflexive (ω^ a + b [ r ]) (<₃ e h) = <-is-irreflexive b h

<-trans : {a b c : Cnf} → a < b → b < c → a < c
<-trans <₁ (<₂ k) = <₁
<-trans <₁ (<₃ e k) = <₁
<-trans (<₂ h) (<₂ k) = <₂ (<-trans h k)
<-trans (<₂ h) (<₃ refl k) = <₂ h
<-trans (<₃ refl h) (<₂ k) = <₂ k
<-trans (<₃ refl h) (<₃ refl k) = <₃ refl (<-trans h k)

<-is-transitive : is-transitive
<-is-transitive a b c = <-trans

\end{code}

■ The order is proposition-valued.

We prove propositionality mutually with decidable equality and sethood
of Cnf.

\begin{code}

mutual

 Cnf-is-discrete : is-discrete Cnf
 Cnf-is-discrete 𝟎 𝟎 = inl refl
 Cnf-is-discrete 𝟎 (ω^ b + d [ s ]) = inr 𝟎-is-not-ω^+
 Cnf-is-discrete (ω^ a + c [ r ]) 𝟎 = inr ω^+-is-not-𝟎
 Cnf-is-discrete (ω^ a + 𝟎 [ r ]) (ω^ b + d [ s ])
  = decide (Cnf-is-discrete a b) (Cnf-is-discrete 𝟎 d)
  where
   decide : (a ＝ b) + (a ≠ b) → (𝟎 ＝ d) + (𝟎 ≠ d)
          → (ω^ a + 𝟎 [ r ] ＝ ω^ b + d [ s ])
          + (ω^ a + 𝟎 [ r ] ≠ ω^ b + d [ s ])
   decide (inl refl) (inl refl)
    = inl (ap (ω^ a + 𝟎 [_])
             (≦-is-prop-valued (exponent 𝟎) a r s))
   decide (inl refl) (inr n) = inr (λ q → n (ap remainder q))
   decide (inr n) _ = inr (λ q → n (ap exponent q))
 Cnf-is-discrete (ω^ a + (ω^ u + v [ t ]) [ r ]) (ω^ b + d [ s ])
  = decide (Cnf-is-discrete a b) (Cnf-is-discrete (ω^ u + v [ t ]) d)
  where
   decide : (a ＝ b) + (a ≠ b) → ((ω^ u + v [ t ]) ＝ d) + ((ω^ u + v [ t ]) ≠ d)
          → (ω^ a + (ω^ u + v [ t ]) [ r ] ＝ ω^ b + d [ s ])
          + (ω^ a + (ω^ u + v [ t ]) [ r ] ≠ ω^ b + d [ s ])
   decide (inl refl) (inl refl)
    = inl (ap (ω^ a + (ω^ u + v [ t ]) [_])
             (≦-is-prop-valued (exponent (ω^ u + v [ t ])) a r s))
   decide (inl refl) (inr n) = inr (λ q → n (ap remainder q))
   decide (inr n) _ = inr (λ q → n (ap exponent q))

 normalise : (a b : Cnf) → a ＝ b → a ＝ b
 normalise a b = pr₁ (decidable-types-are-collapsible (Cnf-is-discrete a b))

 normalise-is-constant : (a b : Cnf) (p q : a ＝ b)
                       → normalise a b p ＝ normalise a b q
 normalise-is-constant a b
  = pr₂ (decidable-types-are-collapsible (Cnf-is-discrete a b))

 normalise-canonical : {a b : Cnf} (p : a ＝ b)
                     → p ＝ (normalise a a refl) ⁻¹ ∙ normalise a b p
 normalise-canonical {a} refl = sym-is-inverse (normalise a a refl)

 Cnf-is-set : is-set Cnf
 Cnf-is-set {a} {b} p q
  = normalise-canonical p
    ∙ ap (λ r → (normalise a a refl) ⁻¹ ∙ r)
         (normalise-is-constant a b p q)
    ∙ (normalise-canonical q) ⁻¹

 <-is-prop-valued : is-prop-valued
 <-is-prop-valued _ _ <₁ <₁ = refl
 <-is-prop-valued _ _ (<₂ h) (<₂ k)
  = ap <₂ (<-is-prop-valued _ _ h k)
 <-is-prop-valued _ _ (<₂ h) (<₃ e k)
  = 𝟘-elim (is-irreflexive'-if-irreflexive <-is-irreflexive e h)
 <-is-prop-valued _ _ (<₃ e h) (<₂ k)
  = 𝟘-elim (is-irreflexive'-if-irreflexive <-is-irreflexive e k)
 <-is-prop-valued _ _ (<₃ e h) (<₃ f k)
  = ap (λ q → <₃ q h) (Cnf-is-set e f)
    ∙ ap (<₃ f) (<-is-prop-valued _ _ h k)

 ≦-is-prop-valued : (a b : Cnf) → is-prop (a ≦ b)
 ≦-is-prop-valued a b (inl h) (inl k)
  = ap inl (<-is-prop-valued a b h k)
 ≦-is-prop-valued a b (inl h) (inr e)
  = 𝟘-elim (is-irreflexive'-if-irreflexive <-is-irreflexive (e ⁻¹) h)
 ≦-is-prop-valued a b (inr e) (inl h)
  = 𝟘-elim (is-irreflexive'-if-irreflexive <-is-irreflexive (e ⁻¹) h)
 ≦-is-prop-valued a b (inr e) (inr f) = ap inr (Cnf-is-set e f)

\end{code}

■ The order is trichotomous and extensional.

Trichotomy follows by comparing leading exponents and then remainders.
If two normal forms have the same predecessors, either strict comparison
contradicts irreflexivity, so the normal forms are equal.

\begin{code}

ω^+-＝ : {a b c d : Cnf} {r : exponent c ≦ a} {s : exponent d ≦ b}
       → a ＝ b → c ＝ d → ω^ a + c [ r ] ＝ ω^ b + d [ s ]
ω^+-＝ {a} {b} {c} {d} {r} {s} refl refl
 = ap (ω^ a + c [_]) (≦-is-prop-valued (exponent c) a r s)

<-is-trichotomous : is-trichotomous-order
<-is-trichotomous 𝟎 𝟎 = inr (inl refl)
<-is-trichotomous 𝟎 (ω^ b + d [ s ]) = inl <₁
<-is-trichotomous (ω^ a + c [ r ]) 𝟎 = inr (inr <₁)
<-is-trichotomous (ω^ a + c [ r ]) (ω^ b + d [ s ])
 = compare (<-is-trichotomous a b) (<-is-trichotomous c d)
 where
  compare : in-trichotomy a b → in-trichotomy c d
          → in-trichotomy (ω^ a + c [ r ]) (ω^ b + d [ s ])
  compare (inl h) _ = inl (<₂ h)
  compare (inr (inr h)) _ = inr (inr (<₂ h))
  compare (inr (inl e)) (inl h) = inl (<₃ e h)
  compare (inr (inl e)) (inr (inl f)) = inr (inl (ω^+-＝ e f))
  compare (inr (inl e)) (inr (inr h)) = inr (inr (<₃ (e ⁻¹) h))

<-is-extensional : is-extensional
<-is-extensional a b f g = conclude (<-is-trichotomous a b)
 where
  conclude : in-trichotomy a b → a ＝ b
  conclude (inl h) = 𝟘-elim (<-is-irreflexive a (g a h))
  conclude (inr (inl e)) = e
  conclude (inr (inr h)) = 𝟘-elim (<-is-irreflexive b (f b h))

\end{code}

■ The order is well-founded.

The remainder of a nonzero normal form is strictly below the whole term.
Using this fact, we prove accessibility by nested induction on the leading
exponent and the remainder.

\begin{code}

remainder-below : (a b : Cnf) (r : exponent b ≦ a) → b < ω^ a + b [ r ]
remainder-below a 𝟎 r = <₁
remainder-below a (ω^ b + c [ s ]) (inl h) = <₂ h
remainder-below a (ω^ b + c [ s ]) (inr refl)
 = <₃ refl (remainder-below a c s)

𝟎-is-accessible : is-accessible 𝟎
𝟎-is-accessible = acc (λ y ())

mutual

 smaller-exponent-is-accessible
  : {a a' : Cnf} → is-accessible a' → a ＝ a'
  → {b x : Cnf} → is-accessible b → x < a' → (r : exponent b ≦ x)
  → is-accessible (ω^ x + b [ r ])
 smaller-exponent-is-accessible {a} {a'} (acc f) e {b} {x} ab h r
  = acc below
  where
   below : (z : Cnf) → z < ω^ x + b [ r ] → is-accessible z
   below 𝟎 <₁ = 𝟎-is-accessible
   below (ω^ c + d [ s ]) (<₂ k)
    = smaller-exponent-is-accessible (f x h) refl ad k s
    where
     ad : is-accessible d
     ad = below d (<-trans (remainder-below c d s) (<₂ k))
   below (ω^ c + d [ s ]) (<₃ q k)
    = smaller-remainder-is-accessible (f x h) q ab k s

 smaller-remainder-is-accessible
  : {a a' : Cnf} → is-accessible a' → a ＝ a'
  → {c y : Cnf} → is-accessible c → y < c → (r : exponent y ≦ a)
  → is-accessible (ω^ a + y [ r ])
 smaller-remainder-is-accessible {a} aa refl {c} {y} (acc f) h r
  = acc below
  where
   below : (z : Cnf) → z < ω^ a + y [ r ] → is-accessible z
   below 𝟎 <₁ = 𝟎-is-accessible
   below (ω^ b + d [ s ]) (<₂ k)
    = smaller-exponent-is-accessible aa refl ad k s
    where
     ad : is-accessible d
     ad = below d (<-trans (remainder-below b d s) (<₂ k))
   below (ω^ b + d [ s ]) (<₃ refl k)
    = smaller-remainder-is-accessible aa refl (f y h) k s

<-is-well-founded : is-well-founded
<-is-well-founded 𝟎 = 𝟎-is-accessible
<-is-well-founded (ω^ a + b [ r ]) = acc below
 where
  below : (z : Cnf) → z < ω^ a + b [ r ] → is-accessible z
  below 𝟎 <₁ = 𝟎-is-accessible
  below (ω^ c + d [ s ]) (<₂ h)
   = smaller-exponent-is-accessible (<-is-well-founded a) refl ad h s
   where
    ad : is-accessible d
    ad = below d (<-trans (remainder-below c d s) (<₂ h))
  below (ω^ c + d [ s ]) (<₃ e h)
   = smaller-remainder-is-accessible
      (<-is-well-founded a) e (<-is-well-founded b) h s

\end{code}

■ The ordinal of Cantor normal forms

\begin{code}

<-is-well-order : is-well-order
<-is-well-order = <-is-prop-valued
                , <-is-well-founded
                , <-is-extensional
                , <-is-transitive

Cnfₒ : Ordinal 𝓤₀
Cnfₒ = Cnf , _<_ , <-is-well-order

\end{code}

■ The weak and split comparisons coincide.

Trichotomy identifies predecessor inclusion ≼ with the split comparison ≦.
This also gives mixed transitivity for the weak order.

\begin{code}

≦-gives-≼ : {a b : Cnf} → a ≦ b → a ≼ b
≦-gives-≼ (inl h) = <-gives-≼ <-is-transitive h
≦-gives-≼ (inr e) = ≼-refl-＝ (e ⁻¹)

≼-gives-≦ : {a b : Cnf} → a ≼ b → a ≦ b
≼-gives-≦ {a} {b} h = decide (<-is-trichotomous a b)
 where
  decide : in-trichotomy a b → a ≦ b
  decide (inl l) = inl l
  decide (inr (inl e)) = inr (e ⁻¹)
  decide (inr (inr l)) = 𝟘-elim (<-is-irreflexive b (h b l))

≦-iff-≼ : (a b : Cnf) → (a ≦ b ↔ a ≼ b)
≦-iff-≼ a b = ≦-gives-≼ , ≼-gives-≦

≼-<-gives-< : (a b c : Cnf) → a ≼ b → b < c → a < c
≼-<-gives-< a b c h k = decide (≼-gives-≦ h)
 where
  decide : a ≦ b → a < c
  decide (inl l) = <-trans l k
  decide (inr refl) = k

\end{code}

■ The successor in Cnf is strong and exact.

The successor adds one at the end of a normal form.  Its strict predecessors
are exactly the normal forms weakly below the original input.

\begin{code}

mutual

 succ : Cnf → Cnf
 succ 𝟎 = ω^ 𝟎 + 𝟎 [ inr refl ]
 succ (ω^ a + b [ r ]) = ω^ a + succ b [ succ-exponent-bound a b r ]

 succ-exponent-bound : (a b : Cnf) → exponent b ≦ a → exponent (succ b) ≦ a
 succ-exponent-bound a 𝟎 r = r
 succ-exponent-bound a (ω^ b + c [ s ]) r = r

<-succ : (a : Cnf) → a < succ a
<-succ 𝟎 = <₁
<-succ (ω^ a + b [ r ]) = <₃ refl (<-succ b)

<-succ-gives-≦ : (a b : Cnf) → a < succ b → a ≦ b
<-succ-gives-≦ 𝟎 𝟎 h = inr refl
<-succ-gives-≦ (ω^ a + c [ r ]) 𝟎 (<₂ ())
<-succ-gives-≦ (ω^ a + c [ r ]) 𝟎 (<₃ e ())
<-succ-gives-≦ 𝟎 (ω^ b + d [ s ]) h = inl <₁
<-succ-gives-≦ (ω^ a + c [ r ]) (ω^ b + d [ s ]) (<₂ h) = inl (<₂ h)
<-succ-gives-≦ (ω^ a + c [ r ]) (ω^ b + d [ s ]) (<₃ e h)
 = decide (<-succ-gives-≦ c d h)
 where
  decide : c ≦ d → (ω^ a + c [ r ]) ≦ (ω^ b + d [ s ])
  decide (inl k) = inl (<₃ e k)
  decide (inr q) = inr (ω^+-＝ (e ⁻¹) q)

succ-predecessors : (a b : Cnf) → (b < succ a ↔ b ≼ a)
succ-predecessors a b
 = (λ h → ≦-gives-≼ (<-succ-gives-≦ b a h)) ,
   (λ h → ≼-<-gives-< b a (succ a) h (<-succ a))

\end{code}

We express the results using the predicates from Ordinals.Successors.
Only that module requires a univalence parameter; the construction and
order proofs above do not.

\begin{code}

open import UF.Univalence
import Ordinals.Successors

module _ (ua : Univalence) where

 open Ordinals.Successors.Successors ua Cnfₒ

 succ-is-strong-succ : (a : Cnf) → succ a is-strong-succ-of a
 succ-is-strong-succ a
  = <-succ a , (λ b → pr₁ (succ-predecessors a b)) , least
  where
   least : (b : Cnf) → a < b → succ a ≼ b
   least b h c k = ≼-<-gives-< c a b (pr₁ (succ-predecessors a c) k) h

 succ-is-exact-succ : (a : Cnf) → succ a is-exact-succ-of a
 succ-is-exact-succ = succ-predecessors

\end{code}
