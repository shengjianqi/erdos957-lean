import PacketMetricLocality
import DiameterAxisSeparation
import LargeScaleReduction

/-! Diameter axes of actual packet sources that charge the same receiver
have positive inner product. This is an orientation statement, not a
cyclic hull locality or receiver capacity assertion. -/

namespace Erdos957

/-- Two diameter endpoints within four reference lengths have compatible
diameter axes when the diameter exceeds ten reference lengths. The scale
threshold remains the one supplied by the existing large-cardinality bound. -/
theorem diameter_axes_inner_pos_of_dist_le_four_min
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u w j k : E) (D r : ℝ) (hr : 0 ≤ r)
    (huj : dist u j = D) (hwk : dist w k = D)
    (hjk : dist j k ≤ D) (hnear : dist u w ≤ 4 * r)
    (hlong : 10 * r < D) :
    0 < inner ℝ (j - u) (k - w) := by
  have hD : 0 < D := by linarith
  have hA : ‖j - u‖ = D := by
    simpa only [dist_eq_norm, norm_sub_rev] using huj
  have hB : ‖k - w‖ = D := by
    simpa only [dist_eq_norm, norm_sub_rev] using hwk
  have hdiff : (j - u) - (k - w) = (j - k) + (w - u) := by abel
  have hbound : ‖(j - u) - (k - w)‖ ≤ D + 4 * r := by
    rw [hdiff]
    calc
      ‖(j - k) + (w - u)‖ ≤ ‖j - k‖ + ‖w - u‖ := norm_add_le _ _
      _ ≤ D + 4 * r := by
        simpa only [dist_eq_norm, norm_sub_rev] using add_le_add hjk hnear
  have hsq : ‖(j - u) - (k - w)‖ ^ 2 ≤ (D + 4 * r) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hbound
  have hexpand := norm_sub_sq_real (j - u) (k - w)
  rw [hA, hB] at hexpand
  have hprod : 0 < (D - 10 * r) * (D + 2 * r) :=
    mul_pos (by linarith) (by positivity)
  nlinarith only [hsq, hexpand, hprod, sq_nonneg r]

/-- Positive assembled charge certifies that its source is a real diameter
endpoint, independently of how the local packets were selected. -/
theorem localPacketCharge_pos_mem_diameterEndpoints {n : ℕ}
    (p : Fin n → Point) (bad : Finset (Fin n))
    (packets : ∀ u, u ∈ chargeDonors p bad → LocalChargePacket p u)
    {u x : Fin n} (hux : 0 < localPacketCharge p bad packets u x) :
    u ∈ diameterEndpoints p := by
  classical
  by_cases hu : u ∈ chargeDonors p bad
  · exact (Finset.mem_filter.mp hu).1
  · simp only [localPacketCharge, dite_eq_right hu] at hux
    omega

/-- Any chosen diameter partners of two positive sources charging the same
receiver determine axes with positive inner product. -/
theorem localPacketCharge_source_axes_inner_pos {n : ℕ}
    (p : Fin n → Point) (hp : Function.Injective p)
    (bad : Finset (Fin n))
    (packets : ∀ u, u ∈ chargeDonors p bad → LocalChargePacket p u)
    {ij kl : Fin n × Fin n} (hmin : isMinPair p ij) (hmax : isMaxPair p kl)
    (hscale : 10 * pairDist p ij < pairDist p kl)
    {u w x j k : Fin n}
    (hux : 0 < localPacketCharge p bad packets u x)
    (hwx : 0 < localPacketCharge p bad packets w x)
    (huj : (diameterGraph p).Adj u j) (hwk : (diameterGraph p).Adj w k) :
    0 < inner ℝ (p j - p u) (p k - p w) := by
  apply diameter_axes_inner_pos_of_dist_le_four_min
    (p u) (p w) (p j) (p k) (pairDist p kl) (pairDist p ij)
    dist_nonneg
  · exact (diameterGraph_adj_iff_dist_eq p hp hmax u j).mp huj
  · exact (diameterGraph_adj_iff_dist_eq p hp hmax w k).mp hwk
  · exact isMaxPair_dist_le p hmax j k
  · exact localPacketCharge_sources_dist_le_four_min p bad packets hmin hux hwx
  · exact hscale

/-- Above the existing size threshold, actual positive sources charging
the same receiver have compatible diameter axes for every choice of partners. -/
theorem localPacketCharge_source_axes_inner_pos_of_large_card {n : ℕ}
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (bad : Finset (Fin n))
    (packets : ∀ u, u ∈ chargeDonors p bad → LocalChargePacket p u)
    {u w x j k : Fin n}
    (hux : 0 < localPacketCharge p bad packets u x)
    (hwx : 0 < localPacketCharge p bad packets w x)
    (huj : (diameterGraph p).Adj u j) (hwk : (diameterGraph p).Adj w k) :
    0 < inner ℝ (p j - p u) (p k - p w) := by
  obtain ⟨ij, hmin⟩ := exists_min_pair p (by omega : 2 ≤ n)
  obtain ⟨kl, hmax⟩ := exists_max_pair p (by omega : 2 ≤ n)
  exact localPacketCharge_source_axes_inner_pos p hp bad packets hmin hmax
    (ten_mul_min_lt_max_of_large_card p hp hn hmin hmax) hux hwx huj hwk

/-- The positive transfers themselves supply actual diameter partners;
their compatible axes require no separate source-membership assumptions. -/
theorem localPacketCharge_sources_exist_compatible_diameter_axes {n : ℕ}
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (bad : Finset (Fin n))
    (packets : ∀ u, u ∈ chargeDonors p bad → LocalChargePacket p u)
    {u w x : Fin n}
    (hux : 0 < localPacketCharge p bad packets u x)
    (hwx : 0 < localPacketCharge p bad packets w x) :
    ∃ j k : Fin n, (diameterGraph p).Adj u j ∧ (diameterGraph p).Adj w k ∧
      0 < inner ℝ (p j - p u) (p k - p w) := by
  obtain ⟨j, huj⟩ := (mem_diameterEndpoints_iff_exists_adj p u).mp
    (localPacketCharge_pos_mem_diameterEndpoints p bad packets hux)
  obtain ⟨k, hwk⟩ := (mem_diameterEndpoints_iff_exists_adj p w).mp
    (localPacketCharge_pos_mem_diameterEndpoints p bad packets hwx)
  exact ⟨j, k, huj, hwk,
    localPacketCharge_source_axes_inner_pos_of_large_card p hp hn bad packets hux hwx huj hwk⟩

end Erdos957
