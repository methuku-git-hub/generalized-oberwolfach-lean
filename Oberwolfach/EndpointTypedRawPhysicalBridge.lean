module

public import Oberwolfach.EndpointTypedRowPhysicalIdentity
public import Oberwolfach.EndpointTypedIndexPhysicalIdentity
public import Oberwolfach.RawOrdinaryPatternSampling

@[expose] public section
/-! Pointwise identities on the original raw sample, before any later edit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem endpoint_typed_raw_physical_row (P F:SimpleGraph V) (A:Finset V) (B:Finset U)
    (x v:V) (weight:Sym2 (V⊕U)→ℝ) (D:ℝ) (π:Equiv.Perm V) (d:ℕ)
    (j:Color) (σ:RawWheelOutcome V U Γ Color):
    rawOrdinaryPatternSum P π d
      (fun z:EndpointRowCandidates (endpointEligibleGraph P F (A∩P.neighborFinset x) x) A B v=>
        endpointRowResources x v z.val.2 z.val.1)
      (fun z=>weight s(Sum.inl v,Sum.inl z.val.2)/D) j σ=
    endpointRowPotential (ordinaryPhysicalGraph P (fun _ _=>False))
      (ordinaryPhysicalGraph (rawWheelGraph P σ) (fun _ _=>False))
      (ordinaryPhysicalGraph ⊥ (rawWheelSpokes π d σ j)) (ordinaryPhysicalGraph F (fun _ _=>False))
      (A.image Sum.inl) (B.image Sum.inr) (Sum.inl x) (Sum.inl v) weight D:=by
  simpa only [rawOrdinaryPatternSum,supportedPatternSum] using
    endpoint_typed_row_physical_identity P (rawWheelGraph P σ) F (rawWheelSpokes π d σ j) A B x v weight D

theorem endpoint_typed_raw_physical_index (P F:SimpleGraph V) (A:Finset V) (x:V) (u:U)
    (weight:Sym2 (V⊕U)→ℝ) (D:ℝ) (π:Equiv.Perm V) (d:ℕ)
    (j:Color) (σ:RawWheelOutcome V U Γ Color):
    rawOrdinaryPatternSum P π d
      (fun e:↥(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeFinset=>endpointIndexResources x u e.val)
      (fun e=>weight (Sym2.map Sum.inl e.val)/D) j σ=
    endpointIndexPotential (ordinaryPhysicalGraph P (fun _ _=>False))
      (ordinaryPhysicalGraph (rawWheelGraph P σ) (fun _ _=>False))
      (ordinaryPhysicalGraph ⊥ (rawWheelSpokes π d σ j)) (ordinaryPhysicalGraph F (fun _ _=>False))
      (A.image Sum.inl) (Sum.inl x) (Sum.inr u) weight D:=by
  simpa only [rawOrdinaryPatternSum,supportedPatternSum] using
    endpoint_typed_index_physical_identity P (rawWheelGraph P σ) F (rawWheelSpokes π d σ j) A x u weight D
end Oberwolfach
