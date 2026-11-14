module

public import Oberwolfach.ActualBoundaryEndpointHubsDependent
public import Oberwolfach.ActualPrescribedBoundaryMultiplicityDependent

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_prescribed_multiplicity_from_boundary_and_missing_dependent
    {V U Color:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U] [Fintype Color]
    {X:U→Type} [∀w,Fintype (X w)] [∀w,DecidableEq (X w)]
    {K J:U→Type} [∀w,DecidableEq (K w)] [∀w,DecidableEq (J w)]
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Bool Color)
    (F:∀w,SimpleGraph (X w)) (data:∀w,ActualResidualData (K:=K w) (J:=J w) (F w))
    (ψ:∀w,X w→V) (root:∀w,K w→V) (colour:∀w,K w→Bool) (H:Finset U)
    (hroot:∀w i,i∈(data w).s₁∪(data w).s₂→ rawIntervalColouredStart π d (fun e=>σ (w,e)) (root w i) (colour w i))
    (hfirst:∀w i,i∈(data w).s₁∪(data w).s₂→ ((data w).P i |>.getVert 2)∈(data w).prescribed→ψ w ((data w).P i |>.getVert 2)=root w i)
    (hlast:∀w i,i∈(data w).s₁∪(data w).s₂→ ((data w).P i |>.getVert (2+(data w).c*(data w).d))∈(data w).prescribed→ψ w ((data w).P i |>.getVert (2+(data w).c*(data w).d))=(π^d) (root w i))
    (x:V) (B C:ℝ)
    (hboundary:((rawIntervalBoundaryHubSet π d σ H x).card:ℝ)≤B)
    (hmissing:((H.filter (fun w=>∃i∈(data w).s₂,∃j:ℕ,j<(data w).d ∧ j∉(data w).T i ∧
      (((data w).P i |>.getVert (2+(data w).c*j))∈(data w).prescribed ∧ x=ψ w ((data w).P i |>.getVert (2+(data w).c*j)) ∨
       ((data w).P i |>.getVert (2+(data w).c*(j+1)))∈(data w).prescribed ∧ x=ψ w ((data w).P i |>.getVert (2+(data w).c*(j+1)))))).card:ℝ)≤C):
    ((H.filter (fun w=>x∈(residualSubtypeSet (data w).remaining (data w).prescribed).image (fun y=>ψ w y.1))).card:ℝ)≤B+C:=by
  have hh:=actual_prescribed_boundary_multiplicity_dependent F data ψ H x
  have hsub:=actual_boundary_endpoint_hubs_subset_dependent π d σ F data ψ root colour H hroot hfirst hlast x
  have hcard:((H.filter (fun w=>∃i∈(data w).s₁∪(data w).s₂,
      ((data w).P i |>.getVert 2)∈(data w).prescribed ∧ x=ψ w ((data w).P i |>.getVert 2) ∨
      ((data w).P i |>.getVert (2+(data w).c*(data w).d))∈(data w).prescribed ∧ x=ψ w ((data w).P i |>.getVert (2+(data w).c*(data w).d)))).card:ℝ)≤
      (rawIntervalBoundaryHubSet π d σ H x).card:=by exact_mod_cast Finset.card_le_card hsub
  dsimp only at hh
  linarith only [hh,hcard,hboundary,hmissing]
end Oberwolfach
