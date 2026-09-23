import CertifiedLowCentral
import CertifiedCentralPackets
import CertifiedSharedSixReflection
import SharedFiveCenterFamily
import AdjacentDonorReduction

/-! A common type for the retained charging-rule certificates. Shared-five
donors always use the center-indexed choice. Coverage and global capacity
are separate theorems. -/

namespace Erdos957

/-- The explicit rules used by one donor. A shared-five constructor retains
availability of the center's single choice, rather than a new independent pair. -/
inductive CertifiedDonorRule {n : ℕ} (p : Fin n → Point)
    (u q : Fin n) (height : Fin n → ℝ) where
  | low (choice : CertifiedLowCentralPacket p u q)
  | unique (choice : CertifiedCentralPacket p u q height)
      (high : 5 ≤ (nearestGraph p).degree q)
  | sharedFive (available : Nonempty (SharedFiveCenterChoice p q))
      (endpoint : u ∈ diameterEndpoints p) (central : (nearestGraph p).Adj q u)
  | sharedSix {w : Fin n} (choice : SharedSixPacketChoice p w u q)
  | reflectedSharedSix {w : Fin n} (choice : ReflectedSharedSixPacketChoice p w u q)

noncomputable def CertifiedDonorRule.packet {n : ℕ}
    {p : Fin n → Point} {u q : Fin n} {height : Fin n → ℝ}
    (rule : CertifiedDonorRule p u q height) : LocalChargePacket p u :=
  match rule with
  | .low choice => choice.packet
  | .unique choice _ => choice.packet
  | .sharedFive available endpoint central =>
      (selectedSharedFiveCenter p q available).packetFor u endpoint central
  | .sharedSix choice => choice.packet
  | .reflectedSharedSix choice => choice.packet

/-- The shared-five projection is the already fixed center's charge. -/
theorem CertifiedDonorRule.sharedFive_weight {n : ℕ}
    (p : Fin n → Point) (u q : Fin n) (height : Fin n → ℝ)
    (available : Nonempty (SharedFiveCenterChoice p q))
    (hu : u ∈ diameterEndpoints p) (hqu : (nearestGraph p).Adj q u)
    (x : Fin n) :
    (CertifiedDonorRule.sharedFive (height := height) available hu hqu).packet.weight x =
      (selectedSharedFiveCenter p q available).charge u x :=
  (selectedSharedFiveCenter p q available).packetFor_weight u hu hqu x

/-- All already established direct branches return their full certificates;
the remaining alternative retains an actual shared endpoint witness. -/
theorem certified_direct_rule_or_shared {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {bad : Finset (Fin n)} {u : Fin n} (ctx : DonorContext p bad u)
    (height : Fin n → ℝ) :
    Nonempty (CertifiedDonorRule p u ctx.q height) ∨
      (((nearestGraph p).degree ctx.q = 5 ∨ (nearestGraph p).degree ctx.q = 6) ∧
        SharedD p u ctx.q) := by
  classical
  by_cases hlow : (nearestGraph p).degree ctx.q ≤ 4
  · exact Or.inl ⟨.low (certifiedLowCentralPacket_of_context p ctx hlow)⟩
  have hhigh : 5 ≤ (nearestGraph p).degree ctx.q := by omega
  by_cases hunique : UniqueD p u ctx.q
  · exact Or.inl ⟨.unique (certifiedCentralPacket_of_uniqueD p hn hp ctx hunique height)
      hhigh⟩
  right
  refine ⟨?_, sharedD_of_not_uniqueD p u ctx.q hunique⟩
  have hle := ctx.central_degree_le_six
  omega

/-- A genuine adjacent shared triangle connects either orientation to the
full certificates. No good-neighborhood premise is imposed on the partner. -/
theorem certifiedDonorRule_of_adjacent_shared {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ i, 0 < hullExteriorAngle p v i)
    (i : Fin h) (ctx : DonorContext p (tightHullBadVertices p v) (v i))
    (height : Fin n → ℝ)
    (hdegree : (nearestGraph p).degree ctx.q = 5 ∨ (nearestGraph p).degree ctx.q = 6)
    (w : Fin n) (hwD : w ∈ diameterEndpoints p)
    (huw : (nearestGraph p).Adj (v i) w) (hqw : (nearestGraph p).Adj ctx.q w)
    (hwhere : w = v (i + 1) ∨ w = v (i - 1)) :
    Nonempty (CertifiedDonorRule p (v i) ctx.q height) := by
  rcases hdegree with hfive | hsix
  · have havailable : Nonempty (SharedFiveCenterChoice p ctx.q) := by
      rcases hwhere with rfl | rfl
      · exact sharedFiveCenterChoice_nonempty_of_either_tight_flat_endpoint
          p hp hn v hv hh hsupport hpos i ctx.q huw hqw ctx.central_adj.symm
          hfive (Or.inl ctx.outside_bad) hwD ctx.endpoint
      · apply sharedFiveCenterChoice_nonempty_of_either_tight_flat_endpoint
          p hp hn v hv hh hsupport hpos (i - 1) ctx.q
        · simpa only [sub_add_cancel] using huw.symm
        · simpa only [sub_add_cancel] using ctx.central_adj.symm
        · exact hqw
        · exact hfive
        · exact Or.inr (by simpa only [sub_add_cancel] using ctx.outside_bad)
        · simpa only [sub_add_cancel] using ctx.endpoint
        · exact hwD
    exact ⟨.sharedFive havailable ctx.endpoint ctx.central_adj.symm⟩
  · rcases hwhere with rfl | rfl
    · exact ⟨.sharedSix (sharedSixPacketChoice_of_large_card
        p hp hn v hv hh hrange hsupport hpos i ctx.q huw hqw ctx.central_adj.symm
        hsix ctx.outside_bad hwD)⟩
    · exact ⟨.reflectedSharedSix (reflectedSharedSixPacketChoice_of_large_card
        p hp hn v hv hh hrange hsupport hpos i ctx.q huw hqw ctx.central_adj.symm
        hsix ctx.outside_bad hwD)⟩

end Erdos957
