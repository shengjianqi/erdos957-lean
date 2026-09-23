import SupportingFamilyCapacity

/-! The unconditional extreme-distance product bound. All size, collinearity,
hull and receiver-capacity obligations are discharged in this module's dependencies. -/

namespace Erdos957

/-- When every diameter endpoint is exceptional, the zero assignment is valid. -/
noncomputable def all_exceptional_charge_certificate {n : ℕ}
    (p : Fin n → Point) : ChargeCertificate p where
  bad := diameterEndpoints p
  charge := fun _ _ => 0
  source := by
    intro u hu
    obtain ⟨huD, hunot, _⟩ := Finset.mem_filter.mp hu
    exact False.elim (hunot huD)
  capacity := by
    intro x hx
    simp

/-- Every injective finite planar configuration has a certificate with the
same exception bound, including small and collinear configurations. -/
theorem exists_uniform_charge_certificate {n : ℕ}
    (p : Fin n → Point) (hp : Function.Injective p) :
    ∃ c : ChargeCertificate p, c.bad.card ≤ 25200 := by
  by_cases hsmall : n ≤ 1681
  · refine ⟨all_exceptional_charge_certificate p, ?_⟩
    change (diameterEndpoints p).card ≤ 25200
    have hc := diameterEndpointCount_le p
    change (diameterEndpoints p).card ≤ n at hc
    omega
  by_cases hcol : Collinear ℝ (Set.range p)
  · refine ⟨all_exceptional_charge_certificate p, ?_⟩
    change (diameterEndpoints p).card ≤ 25200
    have hc := diameterEndpointCount_le_two_of_collinear p hp hcol
    change (diameterEndpoints p).card ≤ 2 at hc
    omega
  have hn : 1681 < n := by omega
  have hh := hullVertexCount_ge_three_of_noncollinear p hcol
  letI : NeZero (hullVertexCount p) := ⟨by omega⟩
  obtain ⟨v, hv, hrange, hsupport, hpos, _hsum, hcard, _hsub, _hgood⟩ :=
    exists_tight_hull_bad_vertices_of_noncollinear p (by omega) hp hcol
  exact ⟨supporting_family_charge_certificate p hp hn v hv hh hrange
    hsupport (fun i => (hpos i).1), hcard⟩

/-- The uniform charging inequality with an explicit, configuration-independent constant. -/
theorem uniform_charging_bound {n : ℕ} (p : Fin n → Point)
    (hn : 2 ≤ n) (hp : Function.Injective p) :
    sMin p + 2 * diameterEndpointCount p ≤ 3 * n + 25200 := by
  obtain ⟨c, hc⟩ := exists_uniform_charge_certificate p hp
  have hb := c.count_bound hn hp
  omega

theorem erdos957_charging_estimate : ChargingEstimate :=
  ⟨25200, fun _ p hn hp _ => uniform_charging_bound p hn hp⟩

/-- Explicit linear-error product bound for unordered closest and farthest pairs. -/
theorem erdos957_product_bound {n : ℕ} (p : Fin n → Point)
    (hn : 2 ≤ n) (hp : Function.Injective p) :
    (sMin p : ℝ) * (sMax p : ℝ) ≤
      (9 / 8 : ℝ) * (n : ℝ) ^ 2 + 25200 * (n : ℝ) := by
  have hb := ExtremeDistances.product_bound_nat n (sMin p) (sMax p)
    (diameterEndpointCount p) 25200 (sMax_le_diameterEndpointCount p hp)
    (diameterEndpointCount_le p) (uniform_charging_bound p hn hp)
  have hr : (8 : ℝ) * (sMin p : ℝ) * (sMax p : ℝ) ≤
      9 * (n : ℝ) ^ 2 + 8 * 25200 * (n : ℝ) := by
    exact_mod_cast hb
  nlinarith

theorem erdos957_quantitative : QuantitativeBound :=
  ⟨25200, by norm_num, fun _ p hn hp => erdos957_product_bound p hn hp⟩

/-- For every positive epsilon one threshold works for all finite planar
configurations: sMin*sMax <= (9/8+epsilon)*n^2. -/
theorem erdos957_asymptotic : AsymptoticBound :=
  asymptotic_of_quantitative erdos957_quantitative

end Erdos957
