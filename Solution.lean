module

public import Mathlib

/-!
# Erdős Problem 657: proof of Straus's construction

Proof of the statement of `Challenge.lean`. The definitions are repeated verbatim.

For `S ⊆ {0, …, k - 1}` let `pt S` be the point with coordinate `√(2^i)` for `i ∈ S` and `0`
otherwise. The squared distance between `pt S` and `pt T` is `∑_{i ∈ S ∆ T} 2^i`, so by uniqueness
of binary expansions the distance determines `S ∆ T`. Two equal sides `pt S pt T` and `pt T pt U`
would give `S ∆ T = T ∆ U`, hence `S = U`; so the `2^k` points have no isosceles triangle. The
distances are determined by the `2^k - 1` nonempty sets `S ∆ T`.
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

namespace Erdos657Proof

open Finset

/-- The coordinate weight `√(2^i)`. -/
noncomputable def w (i : ℕ) : ℝ := Real.sqrt (2 ^ i)

lemma w_sq (i : ℕ) : w i ^ 2 = 2 ^ i := Real.sq_sqrt (by positivity)

/-- The point with coordinate `√(2^i)` for `i ∈ S` and `0` otherwise. -/
noncomputable def pt {k : ℕ} (S : Finset (Fin k)) : ℝ^k :=
  WithLp.toLp 2 fun i ↦ if i ∈ S then w i else 0

lemma pt_apply {k : ℕ} (S : Finset (Fin k)) (i : Fin k) : pt S i = if i ∈ S then w i else 0 :=
  rfl

/-- `g U = ∑_{i ∈ U} 2^i`, the squared distance between `pt S` and `pt T` when `U = S ∆ T`. -/
noncomputable def g {k : ℕ} (U : Finset (Fin k)) : ℝ := ∑ i ∈ U, (2 : ℝ) ^ (i : ℕ)

lemma g_nonneg {k : ℕ} (U : Finset (Fin k)) : 0 ≤ g U :=
  sum_nonneg fun _ _ ↦ by positivity

/-- Binary expansions are unique. -/
lemma g_injective (k : ℕ) : Function.Injective (g (k := k)) := by
  intro U V h
  have hN : ∑ i ∈ U.map Fin.valEmbedding, 2 ^ i = ∑ i ∈ V.map Fin.valEmbedding, 2 ^ i := by
    simp only [sum_map, Fin.valEmbedding_apply]
    simp only [g] at h
    exact_mod_cast h
  exact map_injective Fin.valEmbedding (geomSum_injective le_rfl hN)

lemma dist_pt {k : ℕ} (S T : Finset (Fin k)) :
    dist (pt S) (pt T) = Real.sqrt (g (symmDiff S T)) := by
  rw [EuclideanSpace.dist_eq]
  congr 1
  have h : ∀ i, dist (pt S i) (pt T i) ^ 2 =
      if i ∈ symmDiff S T then (2 : ℝ) ^ (i : ℕ) else 0 := by
    intro i
    rw [Real.dist_eq, sq_abs, pt_apply, pt_apply]
    by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp [hS, hT, w_sq, Finset.mem_symmDiff]
  rw [sum_congr rfl fun i _ ↦ h i, sum_ite_mem, univ_inter, g]

lemma symmDiff_eq_of_dist_eq {k : ℕ} {S T U V : Finset (Fin k)}
    (h : dist (pt S) (pt T) = dist (pt U) (pt V)) : symmDiff S T = symmDiff U V := by
  rw [dist_pt, dist_pt] at h
  exact g_injective k ((Real.sqrt_inj (g_nonneg _) (g_nonneg _)).1 h)

lemma pt_injective (k : ℕ) : Function.Injective (pt (k := k)) := by
  intro S T h
  have h0 : symmDiff S T = symmDiff T T :=
    symmDiff_eq_of_dist_eq (by rw [h])
  rwa [symmDiff_self, symmDiff_eq_bot] at h0

lemma card_A (k : ℕ) : #(univ.image pt : Finset (ℝ^k)) = 2 ^ k := by
  rw [card_image_of_injective _ (pt_injective k), card_univ, Fintype.card_finset,
    Fintype.card_fin]

lemma isIsoscelesFree_A (k : ℕ) : ((univ.image pt : Finset (ℝ^k)) : Set (ℝ^k)).IsIsoscelesFree := by
  unfold Set.IsIsoscelesFree Set.Triplewise
  intro x hx y hy z hz hxy hyz hxz hiso
  simp only [coe_image, coe_univ, Set.image_univ, Set.mem_range] at hx hy hz
  obtain ⟨S, rfl⟩ := hx
  obtain ⟨T, rfl⟩ := hy
  obtain ⟨U, rfl⟩ := hz
  unfold IsIsosceles at hiso
  rcases hiso with h | h | h
  · have := symmDiff_eq_of_dist_eq h
    rw [symmDiff_comm T U, symmDiff_left_inj] at this
    exact hxz (congrArg pt this)
  · have := symmDiff_eq_of_dist_eq h
    rw [symmDiff_comm T U, symmDiff_right_inj] at this
    exact hxy (congrArg pt this.symm)
  · have := symmDiff_eq_of_dist_eq h
    rw [symmDiff_comm U S, symmDiff_right_inj] at this
    exact hyz (congrArg pt this.symm)

lemma distinctDistances_A (k : ℕ) : distinctDistances (univ.image pt : Finset (ℝ^k)) ≤ 2 ^ k - 1 := by
  unfold distinctDistances distanceSet
  have hsub : (univ.image pt : Finset (ℝ^k)).offDiag.image
      (fun pair : (ℝ^k) × (ℝ^k) ↦ dist pair.1 pair.2) ⊆
      (univ.erase ∅).image fun U : Finset (Fin k) ↦ Real.sqrt (g U) := by
    intro d hd
    rw [mem_image] at hd
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := hd
    rw [mem_offDiag] at hxy
    obtain ⟨hx, hy, hne⟩ := hxy
    obtain ⟨S, -, rfl⟩ := mem_image.1 hx
    obtain ⟨T, -, rfl⟩ := mem_image.1 hy
    refine mem_image.2 ⟨symmDiff S T, mem_erase.2 ⟨fun h ↦ hne ?_, mem_univ _⟩, (dist_pt S T).symm⟩
    rw [← bot_eq_empty, symmDiff_eq_bot] at h
    rw [h]
  refine (card_le_card hsub).trans (card_image_le.trans ?_)
  rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_finset, Fintype.card_fin]

theorem straus (k : ℕ) :
    ∃ A : Finset (ℝ^k), A.card = 2 ^ k ∧ (A : Set (ℝ^k)).IsIsoscelesFree ∧
      distinctDistances A ≤ 2 ^ k - 1 :=
  ⟨univ.image pt, card_A k, isIsoscelesFree_A k, distinctDistances_A k⟩

end Erdos657Proof

namespace Erdos657

theorem erdos_657.variants.straus (k : ℕ) :
    ∃ A : Finset (ℝ^k), A.card = 2 ^ k ∧ (A : Set (ℝ^k)).IsIsoscelesFree ∧
      distinctDistances A ≤ 2 ^ k - 1 :=
  Erdos657Proof.straus k

end Erdos657
