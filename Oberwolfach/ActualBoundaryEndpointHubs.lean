module

public import Oberwolfach.RawIntervalBoundaryHubsUpper
public import Oberwolfach.ResidualActualData

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_boundary_endpoint_hubs_subset
    {V U Color:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U] [Fintype Color]
    {K J:U→Type} [∀w,DecidableEq (K w)] [∀w,DecidableEq (J w)]
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Bool Color)
    (F:U→SimpleGraph V) (data:∀w,ActualResidualData (K:=K w) (J:=J w) (F w))
    (ψ:∀w,V→V) (root:∀w,K w→V) (colour:∀w,K w→Bool) (H:Finset U)
    (hroot:∀w i,i∈(data w).s₁∪(data w).s₂→ rawIntervalColouredStart π d (fun e=>σ (w,e)) (root w i) (colour w i))
    (hfirst:∀w i,i∈(data w).s₁∪(data w).s₂→ ((data w).P i |>.getVert 2)∈(data w).prescribed→ψ w ((data w).P i |>.getVert 2)=root w i)
    (hlast:∀w i,i∈(data w).s₁∪(data w).s₂→ ((data w).P i |>.getVert (2+(data w).c*(data w).d))∈(data w).prescribed→ψ w ((data w).P i |>.getVert (2+(data w).c*(data w).d))=(π^d) (root w i))
    (x:V):
    H.filter (fun w=>∃i∈(data w).s₁∪(data w).s₂,
      ((data w).P i |>.getVert 2)∈(data w).prescribed ∧ x=ψ w ((data w).P i |>.getVert 2) ∨
      ((data w).P i |>.getVert (2+(data w).c*(data w).d))∈(data w).prescribed ∧ x=ψ w ((data w).P i |>.getVert (2+(data w).c*(data w).d))) ⊆
        rawIntervalBoundaryHubSet π d σ H x:=by
  intro w hw
  obtain ⟨hwH,i,hi,hx⟩:=Finset.mem_filter.mp hw
  apply Finset.mem_filter.mpr
  refine ⟨hwH,colour w i,?_⟩
  rcases hx with hx|hx
  · obtain ⟨hp,hx⟩:=hx
    left
    rw [hfirst w i hi hp] at hx
    simpa only [hx] using hroot w i hi
  · obtain ⟨hp,hx⟩:=hx
    right
    rw [hlast w i hi hp] at hx
    have hrootEq:root w i=(π^d).symm x:=((π^d).apply_eq_iff_eq_symm_apply).mp hx.symm
    simpa only [←hrootEq] using hroot w i hi
end Oberwolfach
