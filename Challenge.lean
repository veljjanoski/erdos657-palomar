module

public import Mathlib

/-!
# Erdős Problem 657: Straus's observation on isosceles-free point sets

A solved statement about Erdős Problem 657
([erdosproblems.com/657](https://www.erdosproblems.com/657)). The definitions, the notation `ℝ^`
and the theorem statement are copied verbatim from
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) (Apache-2.0) at commit
`a64e959c32c270df4dd0d96d2027481f15750534`, with the same names. The files are
`FormalConjecturesForMathlib/Geometry/Euclidean.lean` (notation),
`FormalConjecturesForMathlib/Geometry/Metric.lean` (`distanceSet`, `distinctDistances`),
`FormalConjecturesForMathlib/Data/Set/Triplewise.lean` (`Set.Triplewise`),
`FormalConjecturesForMathlib/Geometry/2d.lean` (`IsIsosceles`, `Set.IsIsoscelesFree`) and
`FormalConjectures/ErdosProblems/657.lean` (the theorem).
-/

@[expose] public section

scoped[EuclideanGeometry] notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

open scoped Finset

section

variable {X : Type*} [MetricSpace X]

/-- The set of distances determined by a finite set of points in a metric space. -/
noncomputable def distanceSet (points : Finset X) : Finset ℝ :=
  points.offDiag.image fun (pair : X × X) => dist pair.1 pair.2

/--
Given a finite set of points in a metric space, we define the number of distinct distances
between pairs of points.
-/
noncomputable def distinctDistances (points : Finset X) : ℕ :=
  #(distanceSet points)

end

namespace Set

variable {α : Type*}

/--
The ternary relation `r` holds triplewise on the set `s`
if `r x y z` for all *distinct* `x y z ∈ s`.
-/
protected def Triplewise (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s → x ≠ y → y ≠ z → x ≠ z → r x y z

end Set

def IsIsosceles {α : Type*} [Dist α] (p q r : α) : Prop :=
  dist p q = dist q r ∨ dist q r = dist r p ∨ dist r p = dist p q

/-- A set is isosceles-free if no three distinct points in it form an isosceles triangle. -/
def Set.IsIsoscelesFree {α : Type*} [Dist α] (A : Set α) : Prop :=
  A.Triplewise fun x y z ↦ ¬ _root_.IsIsosceles x y z

open Filter
open scoped EuclideanGeometry

namespace Erdos657

/--
Straus observed that for every $k$ there is a set of $2^k$ points in $\mathbb{R}^k$ with no
isosceles triangles which determines at most $2^k - 1$ distinct distances.
-/
theorem erdos_657.variants.straus (k : ℕ) :
    ∃ A : Finset (ℝ^k), A.card = 2 ^ k ∧ (A : Set (ℝ^k)).IsIsoscelesFree ∧
      distinctDistances A ≤ 2 ^ k - 1 := by
  sorry

end Erdos657
