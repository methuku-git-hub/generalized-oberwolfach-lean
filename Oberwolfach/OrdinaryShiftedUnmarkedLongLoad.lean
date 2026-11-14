module

public import Oberwolfach.OrdinaryShiftedUnmarkedLoadBridge
public import Oberwolfach.LongRawHubContext

@[expose] public section
/-! Unmarked wheels see the same resource state in the ordinary and long
encodings; shifted arcs and marked spokes never occur in their patterns. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U C:Type} [Fintype U] [DecidableEq U] [Fintype C]

theorem ordinary_shifted_unmarked_load_eq_long
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ) (g j:Bool)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (R:C→Finset ((Fin n×Fin n)⊕(Fin n×U))) (w:C→ℝ)
    (root:LongRawHubResource n U):
    resourcePatternLoad (fun c=>(R c).map ordinaryMarkedResourceEmbedding) w (fun _ _=>true) root
      (typedMarkedResourceState (ordinaryShiftedPairRims P π d raw) (rawMarkedPairSpokes π d raw g j))=
    resourcePatternLoad (fun c=>(R c).map ordinaryMarkedResourceEmbedding) w (fun _ _=>true) root
      (longRawHubState P π d raw g j) :=by
  by_cases hr:∃r,ordinaryMarkedResourceEmbedding r=root
  · obtain ⟨r,rfl⟩:=hr
    have h1:=ordinary_shifted_unmarked_load_bridge P π d g j raw R w r
    have h2:=ordinary_raw_load_in_marked_universe P π d g j raw R w r
    have hh:=h1.trans h2.symm
    convert hh using 1 <;> (try simp only [longRawHubState]) <;> congr! 5
  · have hn:∀r,orderedOrdinaryResourceEmbedding r≠root:=fun r h=>hr ⟨r,h⟩
    have h1:=ordinary_load_zero_at_nonordinary_resource R w (ordinaryShiftedPairRims P π d raw)
      (rawMarkedPairSpokes π d raw g j) root hn
    have h2:=ordinary_load_zero_at_nonordinary_resource R w (rawMarkedPairRims P π d raw)
      (rawMarkedPairSpokes π d raw g j) root hn
    have hh:=h1.trans h2.symm
    convert hh using 1 <;> (try simp only [longRawHubState]) <;> congr! 5
end Oberwolfach
