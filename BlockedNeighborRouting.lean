import NeighborRoutingCapacity

namespace Erdos957

theorem certified_family_total_le_unblocked_neighbors
    {n : ℕ} (p : Fin n → Point) (bad : Finset (Fin n))
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p bad →
      CertifiedDonorAssignment p bad u (height u))
    (hcard : ∀ y, (directChargeSources p bad y).card ≤ 2) (x : Fin n)
    (blocked : Finset (Fin n))
    (hblocked : ∀ y ∈ blocked, y ∉ diameterEndpoints p ∧
      (5 < (nearestGraph p).degree y ∨
        ∀ a, (nearestGraph p).Adj y a → a ∉ diameterEndpoints p)) :
    ∑ u ∈ chargeDonors p bad,
      localPacketCharge p bad (certifiedFamilyPackets p bad height assignments) u x ≤
      2 * ((nearestGraph p).neighborFinset x \ blocked).card := by
  classical
  let S := chargeDonors p bad
  let packets := certifiedFamilyPackets p bad height assignments
  let f := fun u => localPacketCharge p bad packets u x
  let route := fun u => if hu : u ∈ S then
    if (nearestGraph p).Adj u x then u else (packets u hu).left else u
  let N := (nearestGraph p).neighborFinset x \ blocked
  have hroute (u : Fin n) (hu : u ∈ S) (hpos : 0 < f u) : route u ∈ N := by
    apply Finset.mem_sdiff.mpr
    constructor
    · apply ((nearestGraph p).mem_neighborFinset x (route u)).mpr
      dsimp only [route]
      rw [dite_eq_left hu]
      by_cases hadj : (nearestGraph p).Adj u x
      · simpa only [ite_eq_left hadj] using hadj.symm
      · rw [ite_eq_right hadj]
        exact ((assignments u hu).rule.indirect_left_adj_receiver x
          (by simpa only [f, localPacketCharge, dite_eq_left (show u ∈ chargeDonors p bad from hu),
            packets, certifiedFamilyPackets, CertifiedDonorAssignment.packet] using hpos) hadj).symm
    · intro hmem
      have huD := (Finset.mem_filter.mp hu).1
      by_cases hadj : (nearestGraph p).Adj u x
      · have hm : u ∈ blocked := by simpa only [route, dite_eq_left hu, ite_eq_left hadj] using hmem
        exact (hblocked u hm).1 huD
      · have hm : (packets u hu).left ∈ blocked := by
          simpa only [route, dite_eq_left hu, ite_eq_right hadj] using hmem
        obtain ⟨_, hbad⟩ := hblocked _ hm
        rcases hbad with hhigh | hno
        · have hlow := (packets u hu).left_degree
          omega
        · have hleft := (assignments u hu).rule.left_adj
          exact hno u hleft.symm huD
  have hfiber (y : Fin n) : ∑ u ∈ S.filter (fun u => route u = y), f u ≤ 2 := by
    by_cases hyD : y ∈ diameterEndpoints p
    · have hsingle (u : Fin n) (hu : u ∈ S.filter (fun u => route u = y)) : u = y := by
        obtain ⟨hu, hry⟩ := Finset.mem_filter.mp hu
        dsimp only [route] at hry
        rw [dite_eq_left hu] at hry
        by_cases hadj : (nearestGraph p).Adj u x
        · simpa only [ite_eq_left hadj] using hry
        · rw [ite_eq_right hadj] at hry
          exact False.elim ((packets u hu).left_outside (hry.symm ▸ hyD))
      calc
        _ ≤ ∑ u ∈ S.filter (fun u => route u = y), if u = y then 2 else 0 := by
          apply Finset.sum_le_sum
          intro u hu
          rw [ite_eq_left (hsingle u hu)]
          have hud := (Finset.mem_filter.mp hu).1
          simp only [f, localPacketCharge, dite_eq_left hud, LocalChargePacket.weight]
          split_ifs <;> omega
        _ ≤ 2 := by simp only [Finset.sum_ite_eq']; split_ifs <;> omega
    · have hind (u : Fin n) (hu : u ∈ S.filter (fun u => route u = y)) :
          ¬ (nearestGraph p).Adj u x ∧ (nearestGraph p).Adj u y := by
        obtain ⟨hu, hry⟩ := Finset.mem_filter.mp hu
        dsimp only [route] at hry
        rw [dite_eq_left hu] at hry
        have hnot : ¬ (nearestGraph p).Adj u x := by
          intro hadj
          have huy : u = y := by simpa only [ite_eq_left hadj] using hry
          exact hyD (huy ▸ (Finset.mem_filter.mp hu).1)
        rw [ite_eq_right hnot] at hry
        refine ⟨hnot, ?_⟩
        have ht := (assignments u hu).rule.left_adj
        change (nearestGraph p).Adj u (packets u hu).left at ht
        simpa only [hry] using ht
      have hsub : S.filter (fun u => route u = y) ⊆ directChargeSources p bad y := by
        intro u hu
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu).1, (hind u hu).2⟩
      calc
        _ ≤ ∑ _u ∈ S.filter (fun u => route u = y), (1 : ℕ) := by
          apply Finset.sum_le_sum
          intro u hu
          exact certified_family_charge_le_one_of_not_adj p bad height assignments u x (hind u hu).1
        _ = (S.filter (fun u => route u = y)).card := by simp
        _ ≤ (directChargeSources p bad y).card := Finset.card_le_card hsub
        _ ≤ 2 := hcard y
  have hsum : ∑ u ∈ S, f u = ∑ y ∈ N, ∑ u ∈ S.filter (fun u => route u = y), f u := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u hu
    by_cases hpos : 0 < f u
    · simp [hroute u hu hpos]
    · have hz : f u = 0 := by omega
      simp [hz]
  change ∑ u ∈ S, f u ≤ _
  rw [hsum]
  calc
    _ ≤ ∑ _y ∈ N, (2 : ℕ) := Finset.sum_le_sum (fun y _ => hfiber y)
    _ = 2 * ((nearestGraph p).neighborFinset x \ blocked).card := by
      simp [N, Nat.mul_comm]


/-- Two unusable neighbors leave room for at most four units when degree <=4. -/
theorem certified_family_capacity_of_two_blocked_neighbors
    {n : ℕ} (p : Fin n → Point) (bad : Finset (Fin n))
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p bad →
      CertifiedDonorAssignment p bad u (height u))
    (hcard : ∀ y, (directChargeSources p bad y).card ≤ 2)
    (x : Fin n) (hdegree : (nearestGraph p).degree x ≤ 4)
    (y z : Fin n) (hyz : y ≠ z)
    (hxy : (nearestGraph p).Adj x y) (hxz : (nearestGraph p).Adj x z)
    (hyD : y ∉ diameterEndpoints p) (hzD : z ∉ diameterEndpoints p)
    (hy : 5 < (nearestGraph p).degree y)
    (hz : ∀ a, (nearestGraph p).Adj z a → a ∉ diameterEndpoints p) :
    ∑ u ∈ chargeDonors p bad,
      localPacketCharge p bad (certifiedFamilyPackets p bad height assignments) u x ≤
      2 * (6 - (nearestGraph p).degree x) := by
  classical
  have hb : ∀ a ∈ ({y, z} : Finset (Fin n)), a ∉ diameterEndpoints p ∧
      (5 < (nearestGraph p).degree a ∨
        ∀ u, (nearestGraph p).Adj a u → u ∉ diameterEndpoints p) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact ⟨hyD, Or.inl hy⟩
    · exact ⟨hzD, Or.inr hz⟩
  have hc := certified_family_total_le_unblocked_neighbors p bad height assignments
    hcard x {y, z} hb
  have hsub : ({y, z} : Finset (Fin n)) ⊆ (nearestGraph p).neighborFinset x := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    apply ((nearestGraph p).mem_neighborFinset x a).mpr
    rcases ha with rfl | rfl
    · exact hxy
    · exact hxz
  have hcount := Finset.card_sdiff_add_card_eq_card hsub
  rw [show ({y, z} : Finset (Fin n)).card = 2 by simp [hyz],
    (nearestGraph p).card_neighborFinset_eq_degree] at hcount
  omega

end Erdos957



