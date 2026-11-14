module

public import Oberwolfach.ActualPrescribedBoundaryMultiplicity
public import Oberwolfach.RawIntervalBoundaryHubsUpper

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_missing_boundary_hubs_le_spoke_defects
    {V U:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    {K J:U→Type} [∀w,DecidableEq (K w)] [∀w,DecidableEq (J w)]
    (π:Equiv.Perm V) (d:ℕ) (F:U→SimpleGraph V)
    (data:∀w,ActualResidualData (K:=K w) (J:=J w) (F w))
    (ψ:∀w,V→V) (root:∀w,K w→V) (H:Finset U) (Defect:V→U→Prop)
    (hd:∀w,(data w).d=d)
    (hmarker:∀w i,i∈(data w).s₂→∀j≤d,
      ((data w).P i |>.getVert (2+(data w).c*j))∈(data w).prescribed→ψ w ((data w).P i |>.getVert (2+(data w).c*j))=(π^j) (root w i))
    (hmissing:∀w i,i∈(data w).s₂→∀j<d,j∉(data w).T i→Defect ((π^j) (root w i)) w)
    (x:V):
    ((H.filter (fun w=>∃i∈(data w).s₂,∃j:ℕ,j<(data w).d ∧ j∉(data w).T i ∧
      (((data w).P i |>.getVert (2+(data w).c*j))∈(data w).prescribed ∧ x=ψ w ((data w).P i |>.getVert (2+(data w).c*j)) ∨
       ((data w).P i |>.getVert (2+(data w).c*(j+1)))∈(data w).prescribed ∧ x=ψ w ((data w).P i |>.getVert (2+(data w).c*(j+1)))))).card:ℝ) ≤
      ((H.filter (fun w=>Defect x w)).card:ℝ)+(H.filter (fun w=>Defect (π.symm x) w)).card:=by
  let A:=H.filter (fun w=>∃i∈(data w).s₂,∃j:ℕ,j<(data w).d ∧ j∉(data w).T i ∧
      (((data w).P i |>.getVert (2+(data w).c*j))∈(data w).prescribed ∧ x=ψ w ((data w).P i |>.getVert (2+(data w).c*j)) ∨
       ((data w).P i |>.getVert (2+(data w).c*(j+1)))∈(data w).prescribed ∧ x=ψ w ((data w).P i |>.getVert (2+(data w).c*(j+1)))))
  let B:=H.filter (fun w=>Defect x w)
  let C:=H.filter (fun w=>Defect (π.symm x) w)
  have hsub:A⊆B∪C:=by
    intro w hw
    obtain ⟨hwH,i,hi,j,hj,hnot,hx⟩:=Finset.mem_filter.mp hw
    have hjd:j<d:=by simpa only [hd w] using hj
    have hdef:=hmissing w i hi j hjd hnot
    rcases hx with hx|hx
    · obtain ⟨hp,hx⟩:=hx
      apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      refine ⟨hwH,?_⟩
      have heq:=hmarker w i hi j (by omega) hp
      rw [heq] at hx
      simpa only [hx] using hdef
    · obtain ⟨hp,hx⟩:=hx
      apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨hwH,?_⟩
      have heq:=hmarker w i hi (j+1) (by omega) hp
      rw [heq,pow_succ',Equiv.Perm.mul_apply] at hx
      have hx':(π^j) (root w i)=π.symm x:=π.apply_eq_iff_eq_symm_apply.mp hx.symm
      simpa only [←hx'] using hdef
  have hh:A.card≤B.card+C.card:=(Finset.card_le_card hsub).trans (Finset.card_union_le B C)
  exact_mod_cast hh
end Oberwolfach
