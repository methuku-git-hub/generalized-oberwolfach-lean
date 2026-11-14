module

public import Oberwolfach.ActualPrescribedFromBoundaryAndMissing
public import Oberwolfach.ActualBoundaryEndpointHubs
public import Oberwolfach.ActualPrescribedBoundaryMultiplicity
public import Oberwolfach.ActualMissingBoundarySpokeDefect

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_prescribed_multiplicity_from_boundary_spoke_defects
    {V U Color:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U] [Fintype Color]
    {K J:U→Type} [∀w,DecidableEq (K w)] [∀w,DecidableEq (J w)]
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Bool Color)
    (F:U→SimpleGraph V) (data:∀w,ActualResidualData (K:=K w) (J:=J w) (F w))
    (ψ:∀w,V→V) (root:∀w,K w→V) (colour:∀w,K w→Bool) (H:Finset U)
    (hroot:∀w i,i∈(data w).s₁∪(data w).s₂→ rawIntervalColouredStart π d (fun e=>σ (w,e)) (root w i) (colour w i))
    (hfirst:∀w i,i∈(data w).s₁∪(data w).s₂→ ((data w).P i |>.getVert 2)∈(data w).prescribed→ψ w ((data w).P i |>.getVert 2)=root w i)
    (hlast:∀w i,i∈(data w).s₁∪(data w).s₂→ ((data w).P i |>.getVert (2+(data w).c*(data w).d))∈(data w).prescribed→ψ w ((data w).P i |>.getVert (2+(data w).c*(data w).d))=(π^d) (root w i))
    (Defect:V→U→Prop)
    (hd:∀w,(data w).d=d)
    (hmarker:∀w i,i∈(data w).s₂→∀j≤d,
      ((data w).P i |>.getVert (2+(data w).c*j))∈(data w).prescribed→ψ w ((data w).P i |>.getVert (2+(data w).c*j))=(π^j) (root w i))
    (hmissing:∀w i,i∈(data w).s₂→∀j<d,j∉(data w).T i→Defect ((π^j) (root w i)) w)
    (x:V) (B C₀ C₁:ℝ)
    (hboundary:((rawIntervalBoundaryHubSet π d σ H x).card:ℝ)≤B)
    (hdefect₀:((H.filter (fun w=>Defect x w)).card:ℝ)≤C₀)
    (hdefect₁:((H.filter (fun w=>Defect (π.symm x) w)).card:ℝ)≤C₁):
    ((H.filter (fun w=>x∈(residualSubtypeSet (data w).remaining (data w).prescribed).image (fun y=>ψ w y.1))).card:ℝ)≤B+C₀+C₁:=by
  have hmiss:=actual_missing_boundary_hubs_le_spoke_defects π d F data ψ root H Defect hd hmarker hmissing x
  have hbound:=actual_prescribed_multiplicity_from_boundary_and_missing π d σ F data ψ root colour H hroot hfirst hlast x B (C₀+C₁) hboundary (by linarith only [hmiss,hdefect₀,hdefect₁])
  linarith only [hbound]
end Oberwolfach
