module

public import Oberwolfach.ActualPrescribedMarkerBoundary
public import Oberwolfach.ResidualActualData

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_prescribed_boundary_multiplicity_dependent
    {V U:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    {X:U→Type} [∀w,Fintype (X w)] [∀w,DecidableEq (X w)]
    {K J:U→Type} [∀w,DecidableEq (K w)] [∀w,DecidableEq (J w)]
    (F:∀w,SimpleGraph (X w)) (data:∀w,ActualResidualData (K:=K w) (J:=J w) (F w))
    (ψ:∀w,X w→V) (H:Finset U) (x:V):
    let Endpoint:=H.filter (fun w=>∃i∈(data w).s₁∪(data w).s₂,
      ((data w).P i |>.getVert 2)∈(data w).prescribed ∧ x=ψ w ((data w).P i |>.getVert 2) ∨
      ((data w).P i |>.getVert (2+(data w).c*(data w).d))∈(data w).prescribed ∧ x=ψ w ((data w).P i |>.getVert (2+(data w).c*(data w).d)))
    let Missing:=H.filter (fun w=>∃i∈(data w).s₂,∃j:ℕ,j<(data w).d ∧ j∉(data w).T i ∧
      (((data w).P i |>.getVert (2+(data w).c*j))∈(data w).prescribed ∧ x=ψ w ((data w).P i |>.getVert (2+(data w).c*j)) ∨
       ((data w).P i |>.getVert (2+(data w).c*(j+1)))∈(data w).prescribed ∧ x=ψ w ((data w).P i |>.getVert (2+(data w).c*(j+1)))))
    ((H.filter (fun w=>x∈(residualSubtypeSet (data w).remaining (data w).prescribed).image (fun y=>ψ w y.1))).card:ℝ) ≤
      (Endpoint.card:ℝ)+Missing.card:=by
  intro Endpoint Missing
  have hsub:H.filter (fun w=>x∈(residualSubtypeSet (data w).remaining (data w).prescribed).image (fun y=>ψ w y.1)) ⊆ Endpoint∪Missing:=by
    intro w hw
    have hwH: w∈H:=(Finset.mem_filter.mp hw).1
    obtain ⟨v,hv,hx⟩:=Finset.mem_image.mp (Finset.mem_filter.mp hw).2
    have hvp:v.1∈(data w).prescribed:=by simpa [residualSubtypeSet] using hv
    rcases actual_prescribed_marker_boundary (data w) v.1 hvp with hs | hs
    · obtain ⟨i,hi,hh⟩:=hs
      apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      refine ⟨hwH,i,Finset.mem_union_left _ hi,?_⟩
      rcases hh with hh|hh
      · left; refine ⟨by simpa only [hh] using hvp,?_⟩; simpa only [hh] using hx.symm
      · right; refine ⟨by simpa only [hh] using hvp,?_⟩; simpa only [hh] using hx.symm
    · obtain ⟨i,hi,j,hjd,heq,hcases⟩:=hs
      by_cases h0:j=0
      · apply Finset.mem_union_left
        apply Finset.mem_filter.mpr
        refine ⟨hwH,i,Finset.mem_union_right _ hi,Or.inl ?_⟩
        refine ⟨by simpa only [heq,h0,mul_zero,add_zero] using hvp,?_⟩
        simpa only [heq,h0,mul_zero,add_zero] using hx.symm
      by_cases hd:j=(data w).d
      · apply Finset.mem_union_left
        apply Finset.mem_filter.mpr
        refine ⟨hwH,i,Finset.mem_union_right _ hi,Or.inr ?_⟩
        refine ⟨by simpa only [heq,hd] using hvp,?_⟩
        simpa only [heq,hd] using hx.symm
      rcases hcases with h0'|hd'|hmiss|hmiss
      · exact (h0 h0').elim
      · exact (hd hd').elim
      · apply Finset.mem_union_right
        apply Finset.mem_filter.mpr
        refine ⟨hwH,i,hi,j,by omega,hmiss,Or.inl ?_⟩
        refine ⟨by simpa only [heq] using hvp,?_⟩
        simpa only [heq] using hx.symm
      · apply Finset.mem_union_right
        apply Finset.mem_filter.mpr
        refine ⟨hwH,i,hi,j-1,by omega,hmiss,Or.inr ?_⟩
        have he:j-1+1=j:=by omega
        refine ⟨by simpa only [heq,he] using hvp,?_⟩
        simpa only [heq,he] using hx.symm
  have hh: (H.filter (fun w=>x∈(residualSubtypeSet (data w).remaining (data w).prescribed).image (fun y=>ψ w y.1))).card ≤ Endpoint.card+Missing.card:=
    (Finset.card_le_card hsub).trans (Finset.card_union_le Endpoint Missing)
  exact_mod_cast hh
end Oberwolfach
