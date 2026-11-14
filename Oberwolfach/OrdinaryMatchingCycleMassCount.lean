module

public import Oberwolfach.OrdinaryPhysicalUnmarkedPayload

@[expose] public section
/-! The total length of the unmarked payloads at a hub is the sum of the
selected candidate lengths with the same hub and an unmarked tag. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_matching_cycle_mass_count
    (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (RM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→Finset (((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)))
    (state:(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))→Bool)
    (L:Finset (PhysicalSampledCandidate (mixedCandidateResources
      (ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W))) state))
    (u:U) (i₀:Fin K):
    (∑a:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u,
      (longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L u a).1+2)) =
    ∑x∈L,if x.val.1.isSome ∧ ordinaryMixedGenericWheelHub (U:=U) π (3*d) m longPaddedSeedExponent x.val.1 x.val.2=u
      then longPaddedSeedExponent (x.val.1.getD i₀)+2 else 0 :=by
  classical
  let S:=L.filter (fun x=>x.val.1.isSome ∧ ordinaryMixedGenericWheelHub (U:=U) π (3*d) m longPaddedSeedExponent x.val.1 x.val.2=u)
  have he:(Finset.univ:Finset ↥S)=S.attach:=by ext x;simp
  calc
    _ = ∑a:↥S,(longPaddedSeedExponent (a.val.val.1.getD i₀)+2) := by
      apply Finset.sum_congr
      · ext x; simp
      · intro a _
        rw [ordinary_physical_unmarked_payload_index π d m RM state L u a i₀]
    _ = ∑x∈S,(longPaddedSeedExponent (x.val.1.getD i₀)+2) := by
      rw [he]
      simpa using (Finset.sum_attach S (fun x=>longPaddedSeedExponent (x.val.1.getD i₀)+2))
    _ = _ := by
      dsimp only [S]
      exact Finset.sum_filter _ _
end Oberwolfach
