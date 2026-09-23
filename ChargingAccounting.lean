import BoundaryDegree

/-!
Finite bookkeeping for a possible charging proof.  The existence of a
charge assignment is a hypothesis, not a geometric conclusion of this file.
-/

namespace Erdos957

/-- Boundary vertices of degree three cause one unit of excess in the doubled
degree count.  If the nonboundary degree slack covers every nonexceptional
degree-three boundary vertex, the desired edge count follows. -/
theorem finite_degree_charge_accounting {n : ℕ}
    (degree : Fin n → ℕ) (edgeCount : ℕ)
    (D bad : Finset (Fin n))
    (hhandshake : (∑ i : Fin n, degree i) = 2 * edgeCount)
    (hdeg6 : ∀ i, degree i ≤ 6)
    (hdeg3 : ∀ i ∈ D, degree i ≤ 3)
    (hslack : (D.filter (fun i => i ∉ bad ∧ degree i = 3)).card ≤
      ∑ i ∈ (Finset.univ.filter (fun i : Fin n => i ∉ D)), (6 - degree i)) :
    2 * edgeCount + 4 * D.card ≤ 6 * n + bad.card := by
  classical
  let good := D.filter (fun i => i ∉ bad ∧ degree i = 3)
  let outside := Finset.univ.filter (fun i : Fin n => i ∉ D)
  have hpoint (i : Fin n) :
      degree i + (if i ∈ D then 4 else 0) +
          (if i ∈ D then 0 else 6 - degree i) ≤
        6 + (if i ∈ good then 1 else 0) +
          (if i ∈ bad then 1 else 0) := by
    by_cases hi : i ∈ D
    · have h3 := hdeg3 i hi
      by_cases hb : i ∈ bad
      · simp only [hi, hb, ↓reduceIte]
        omega
      · by_cases hd : degree i = 3
        · have hg : i ∈ good := Finset.mem_filter.mpr ⟨hi, hb, hd⟩
          simp only [hi, hb, hg, ↓reduceIte]
          omega
        · have hng : i ∉ good := by simp [good, hd]
          simp only [hi, hb, hng, ↓reduceIte]
          omega
    · have hng : i ∉ good := by simp [good, hi]
      have h6 := hdeg6 i
      simp only [hi, hng, ↓reduceIte]
      omega
  have hsum :
      (∑ i : Fin n,
        (degree i + (if i ∈ D then 4 else 0) +
          (if i ∈ D then 0 else 6 - degree i))) ≤
      (∑ i : Fin n,
        (6 + (if i ∈ good then 1 else 0) +
          (if i ∈ bad then 1 else 0))) := by
    apply Finset.sum_le_sum
    intro i _
    exact hpoint i
  have hDsum : (∑ i : Fin n, if i ∈ D then (4 : ℕ) else 0) = 4 * D.card := by
    simp [mul_comm]
  have hgoodsum : (∑ i : Fin n, if i ∈ good then (1 : ℕ) else 0) = good.card := by
    simp
  have hbadsum : (∑ i : Fin n, if i ∈ bad then (1 : ℕ) else 0) = bad.card := by
    simp
  have houtsidesum :
      (∑ i : Fin n, if i ∈ D then 0 else 6 - degree i) =
        ∑ i ∈ outside, (6 - degree i) := by
    simp [outside, Finset.sum_filter]
  simp only [Finset.sum_add_distrib] at hsum
  rw [hhandshake, hDsum, hgoodsum, hbadsum, houtsidesum] at hsum
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul] at hsum
  have hslack' : good.card ≤ ∑ i ∈ outside, (6 - degree i) := hslack
  have hsum' : 2 * edgeCount + 4 * D.card +
      (∑ i ∈ outside, (6 - degree i)) ≤
      6 * n + good.card + bad.card := by
    simpa [mul_comm] using hsum
  clear hsum hslack
  omega

/-- A doubled-unit charge assignment of size two from each good boundary
vertex into the complement, with receiver capacity twice the available
degree slack, suffices for the required global count. -/
theorem finite_degree_charge_assignment {n : ℕ}
    (degree : Fin n → ℕ) (edgeCount : ℕ)
    (D bad : Finset (Fin n)) (charge : Fin n → Fin n → ℕ)
    (hhandshake : (∑ i : Fin n, degree i) = 2 * edgeCount)
    (hdeg6 : ∀ i, degree i ≤ 6)
    (hdeg3 : ∀ i ∈ D, degree i ≤ 3)
    (hsource : ∀ u ∈ D.filter (fun i => i ∉ bad ∧ degree i = 3),
      ∑ v ∈ Finset.univ.filter (fun i : Fin n => i ∉ D), charge u v = 2)
    (hcapacity : ∀ v ∈ Finset.univ.filter (fun i : Fin n => i ∉ D),
      ∑ u ∈ D.filter (fun i => i ∉ bad ∧ degree i = 3), charge u v ≤
        2 * (6 - degree v)) :
    2 * edgeCount + 4 * D.card ≤ 6 * n + bad.card := by
  classical
  let good := D.filter (fun i => i ∉ bad ∧ degree i = 3)
  let outside := Finset.univ.filter (fun i : Fin n => i ∉ D)
  have htotal : 2 * good.card ≤
      2 * (∑ v ∈ outside, (6 - degree v)) := by
    calc
      2 * good.card = ∑ u ∈ good, ∑ v ∈ outside, charge u v := by
        rw [Finset.sum_congr rfl (by intro u hu; exact hsource u hu)]
        simp [mul_comm]
      _ = ∑ v ∈ outside, ∑ u ∈ good, charge u v := Finset.sum_comm
      _ ≤ ∑ v ∈ outside, 2 * (6 - degree v) := by
        apply Finset.sum_le_sum
        intro v hv
        exact hcapacity v hv
      _ = 2 * (∑ v ∈ outside, (6 - degree v)) := by
        rw [Finset.mul_sum]
  have hslack : good.card ≤ ∑ v ∈ outside, (6 - degree v) := by omega
  exact finite_degree_charge_accounting degree edgeCount D bad
    hhandshake hdeg6 hdeg3 hslack

/-- Instantiation for the nearest-distance graph. The charge assignment
remains explicit, so this does not establish `ChargingEstimate`. -/
theorem nearestGraph_charge_assignment_accounting {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    (bad : Finset (Fin n)) (charge : Fin n → Fin n → ℕ)
    (hsource : ∀ u ∈ (diameterEndpoints p).filter
      (fun i => i ∉ bad ∧ (nearestGraph p).degree i = 3),
      ∑ v ∈ Finset.univ.filter (fun i : Fin n => i ∉ diameterEndpoints p),
        charge u v = 2)
    (hcapacity : ∀ v ∈ Finset.univ.filter
      (fun i : Fin n => i ∉ diameterEndpoints p),
      ∑ u ∈ (diameterEndpoints p).filter
        (fun i => i ∉ bad ∧ (nearestGraph p).degree i = 3), charge u v ≤
        2 * (6 - (nearestGraph p).degree v)) :
    sMin p + 2 * diameterEndpointCount p ≤ 3 * n + bad.card := by
  have h := finite_degree_charge_assignment
    (fun i => (nearestGraph p).degree i) (sMin p)
    (diameterEndpoints p) bad charge
    (nearestGraph_handshake p)
    (nearestGraph_degree_le_six p hn hp)
    (nearestGraph_degree_le_three_of_diameterEndpoint p hn hp)
    hsource hcapacity
  simp only [diameterEndpointCount] at *
  omega

end Erdos957
