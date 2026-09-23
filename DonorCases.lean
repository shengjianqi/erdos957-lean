import FiveCentralCharge
import LocalChargeAssembly
import LargeScaleReduction
import Mathlib.Tactic.Linarith

/-! A complete logical classification of large-configuration charge donors.
The two shared-diameter-neighbor branches are retained as explicit witnesses;
no adjacency or uniqueness of the second diameter endpoint is assumed. -/

namespace Erdos957

/-- `u` is the only diameter endpoint among the nearest neighbors of `q`. -/
def UniqueD {n : ℕ} (p : Fin n → Point) (u q : Fin n) : Prop :=
  ∀ w, (nearestGraph p).Adj q w → w ∈ diameterEndpoints p → w = u

/-- An additional diameter endpoint is a nearest neighbor of `q`. -/
def SharedD {n : ℕ} (p : Fin n → Point) (u q : Fin n) : Prop :=
  ∃ w, w ≠ u ∧ (nearestGraph p).Adj q w ∧ w ∈ diameterEndpoints p

theorem sharedD_of_not_uniqueD {n : ℕ} (p : Fin n → Point)
    (u q : Fin n) (hnot : ¬ UniqueD p u q) : SharedD p u q := by
  classical
  by_contra hshared
  apply hnot
  intro w hqw hw
  by_contra hwu
  exact hshared ⟨w, hwu, hqw, hw⟩

/-- These five alternatives exhaust the possible central-neighbor degrees
and the unique/shared diameter-endpoint split. -/
def DonorFiveWay {n : ℕ} (p : Fin n → Point) (u q : Fin n) : Prop :=
  (nearestGraph p).degree q ≤ 4 ∨
    ((nearestGraph p).degree q = 5 ∧ UniqueD p u q) ∨
    ((nearestGraph p).degree q = 6 ∧ UniqueD p u q) ∨
    ((nearestGraph p).degree q = 5 ∧ SharedD p u q) ∨
    ((nearestGraph p).degree q = 6 ∧ SharedD p u q)

theorem donorFiveWay_of_degree_le_six {n : ℕ} (p : Fin n → Point)
    (u q : Fin n) (hle : (nearestGraph p).degree q ≤ 6) :
    DonorFiveWay p u q := by
  classical
  by_cases hlow : (nearestGraph p).degree q ≤ 4
  · exact Or.inl hlow
  by_cases hfive : (nearestGraph p).degree q = 5
  · by_cases hunique : UniqueD p u q
    · unfold DonorFiveWay
      tauto
    · have hshared := sharedD_of_not_uniqueD p u q hunique
      unfold DonorFiveWay
      tauto
  have hsix : (nearestGraph p).degree q = 6 := by omega
  by_cases hunique : UniqueD p u q
  · unfold DonorFiveWay
    tauto
  · have hshared := sharedD_of_not_uniqueD p u q hunique
    unfold DonorFiveWay
    tauto

/-- Data available for every diameter endpoint that actually needs charge
when the configuration has more than 1681 points. -/
structure DonorContext {n : ℕ} (p : Fin n → Point)
    (bad : Finset (Fin n)) (u : Fin n) where
  donor : u ∈ chargeDonors p bad
  endpoint : u ∈ diameterEndpoints p
  outside_bad : u ∉ bad
  degree_three : (nearestGraph p).degree u = 3
  j : Fin n
  diameter_adj : (diameterGraph p).Adj u j
  minPair : Fin n × Fin n
  minPair_spec : isMinPair p minPair
  long_diameter : 10 * pairDist p minPair < dist (p u) (p j)
  q : Fin n
  central_adj : (nearestGraph p).Adj u q
  central_lo : -Real.pi / 6 < halfplaneArg (p u) (p j - p u) (p q)
  central_hi : halfplaneArg (p u) (p j - p u) (p q) < Real.pi / 6
  central_unique : ∀ k, (nearestGraph p).Adj u k →
    -Real.pi / 6 < halfplaneArg (p u) (p j - p u) (p k) →
    halfplaneArg (p u) (p j - p u) (p k) < Real.pi / 6 → k = q
  central_interior : p q ∈ interior (convexHull ℝ (Set.range p))
  central_outside : q ∉ diameterEndpoints p
  central_degree_le_six : (nearestGraph p).degree q ≤ 6

/-- The fixed-size packing lemma supplies the long-diameter condition, so
every donor has a unique interior central nearest neighbor. -/
noncomputable def donorContext_of_large_card {n : ℕ}
    (p : Fin n → Point) (hp : Function.Injective p)
    (hlarge : 1681 < n) (bad : Finset (Fin n))
    (u : Fin n) (hu : u ∈ chargeDonors p bad) :
    DonorContext p bad u := by
  classical
  have hn : 2 ≤ n := by omega
  have hu' : u ∈ (diameterEndpoints p).filter
      (fun x => x ∉ bad ∧ (nearestGraph p).degree x = 3) := hu
  obtain ⟨huD, hunot, hudeg⟩ := (Finset.mem_filter.mp hu')
  let hj := (mem_diameterEndpoints_iff_exists_adj p u).mp huD
  let j := Classical.choose hj
  have hdiam := Classical.choose_spec hj
  let hij := exists_min_pair p hn
  let ij := Classical.choose hij
  have hmin := Classical.choose_spec hij
  let hkl := exists_max_pair p hn
  let kl := Classical.choose hkl
  have hmax := Classical.choose_spec hkl
  have hten : 10 * pairDist p ij < dist (p u) (p j) := by
    have hratio := ten_mul_min_lt_max_of_large_card p hp hlarge hmin hmax
    have hdist := (diameterGraph_adj_iff_dist_eq p hp hmax u j).mp hdiam
    rw [hdist]
    exact hratio
  have hscale : 2 * pairDist p ij < dist (p u) (p j) := by
    have hr := pairDist_pos p hp hmin.1
    nlinarith [hten]
  let hq := degree_three_middle_neighbor_unique p hn hp hdiam hudeg
  let q := Classical.choose hq
  have hqspec := Classical.choose_spec hq
  have huq := hqspec.1.1
  have hqlo := hqspec.1.2.1
  have hqhi := hqspec.1.2.2
  have hqunique := hqspec.2
  have hinner := diameter_degree_three_central_neighbor_mem_interior
    p hn hp hdiam hudeg ij hmin hscale q huq hqlo hqhi
  refine {
    donor := hu
    endpoint := huD
    outside_bad := hunot
    degree_three := hudeg
    j := j
    diameter_adj := hdiam
    minPair := ij
    minPair_spec := hmin
    long_diameter := hten
    q := q
    central_adj := huq
    central_lo := hqlo
    central_hi := hqhi
    central_unique := ?_
    central_interior := hinner
    central_outside := interior_not_diameterEndpoints p hp q hinner
    central_degree_le_six := nearestGraph_degree_le_six p hn hp q
  }
  intro k hk hklo hkhi
  exact hqunique k ⟨hk, hklo, hkhi⟩

/-- Every large-configuration donor either already has a local packet, or
falls into one of the two still-open shared-neighbor cases with an explicit
second diameter endpoint witness. -/
theorem donor_resolution_of_large_card {n : ℕ}
    (p : Fin n → Point) (hp : Function.Injective p)
    (hlarge : 1681 < n) (bad : Finset (Fin n))
    (u : Fin n) (hu : u ∈ chargeDonors p bad) :
    ∃ ctx : DonorContext p bad u,
      DonorFiveWay p u ctx.q ∧
      (Nonempty (LocalChargePacket p u) ∨
        ((nearestGraph p).degree ctx.q = 5 ∧ SharedD p u ctx.q) ∨
        ((nearestGraph p).degree ctx.q = 6 ∧ SharedD p u ctx.q)) := by
  classical
  let ctx := donorContext_of_large_card p hp hlarge bad u hu
  refine ⟨ctx, donorFiveWay_of_degree_le_six p u ctx.q
    ctx.central_degree_le_six, ?_⟩
  have hn : 2 ≤ n := by omega
  have hscale : 2 * pairDist p ctx.minPair < dist (p u) (p ctx.j) := by
    have hr := pairDist_pos p hp ctx.minPair_spec.1
    nlinarith [ctx.long_diameter]
  by_cases hlow : (nearestGraph p).degree ctx.q ≤ 4
  · left
    exact ⟨localChargePacket_of_central_low_degree p hn hp
      ctx.diameter_adj ctx.degree_three ctx.minPair ctx.minPair_spec
      hscale ctx.central_adj ctx.central_lo ctx.central_hi hlow⟩
  by_cases hunique : UniqueD p u ctx.q
  · left
    exact ⟨localChargePacket_of_unique_central_neighbor p hn hp
      ctx.diameter_adj ctx.degree_three ctx.minPair ctx.minPair_spec
      hscale ctx.central_adj ctx.central_lo ctx.central_hi hunique⟩
  have hshared : SharedD p u ctx.q :=
    sharedD_of_not_uniqueD p u ctx.q hunique
  by_cases hfive : (nearestGraph p).degree ctx.q = 5
  · exact Or.inr (Or.inl ⟨hfive, hshared⟩)
  have hsix : (nearestGraph p).degree ctx.q = 6 := by
    have hle := ctx.central_degree_le_six
    omega
  exact Or.inr (Or.inr ⟨hsix, hshared⟩)

end Erdos957
