module

public import Oberwolfach.RawIntervalAssignedLabelColumn
public import Oberwolfach.RawIntervalStartColumnCount

@[expose] public section
/-! An extended interval contains a vertex either in its labelled part or as
its one additional terminal point. -/
set_option autoImplicit false
set_option maxHeartbeats 9000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def rawIntervalExtendedHubSet {V U Γ Color:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    [Fintype Γ] [Fintype Color] (π:Equiv.Perm V) (d:ℕ)
    (σ:RawIntervalFamilyOutcome V U Γ Color) (x:V) (g:Γ):Finset U:=
  Finset.univ.filter (fun u=>∃a,rawIntervalColouredStart π d (fun e=>σ (u,e)) a g ∧ x∈permutationWindow π 0 d a)

theorem raw_interval_extended_hub_count_bound
    {V U Γ Color:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    [Fintype Γ] [Fintype Color] (π:Equiv.Perm V) (d:ℕ) (hd:0<d)
    (σ:RawIntervalFamilyOutcome V U Γ Color) (x:V) (g:Γ):
    ((rawIntervalExtendedHubSet π d σ x g).card:ℝ)≤
      rawIntervalAssignedLabelColumnCount π d σ x g Finset.univ+
      rawIntervalStartColumnCount π d σ ((π^d).symm x) g Finset.univ:=by
  let A:=rawIntervalExtendedHubSet π d σ x g
  let B:=Finset.univ.filter (fun u=>rawIntervalFamilyState π d σ (x,u)=some (Sum.inl g))
  let C:=Finset.univ.filter (fun u=>rawIntervalColouredStart π d (fun e=>σ (u,e)) ((π^d).symm x) g)
  have hsub:A⊆B∪C:=by
    intro u hu
    obtain ⟨a,ha,hx⟩:=(Finset.mem_filter.mp hu).2
    unfold permutationWindow at hx
    simp only [Nat.zero_add,pow_zero,Equiv.refl_symm,Equiv.refl_apply] at hx
    obtain ⟨j,_,hj⟩:=Finset.mem_image.mp hx
    by_cases hjd:j.val<d
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      apply (rawIntervalState_interval_iff π d (fun e=>σ (u,e)) x g).2
      refine ⟨a,ha,?_⟩
      unfold permutationWindow
      simp only [Nat.zero_add,pow_zero,Equiv.refl_symm,Equiv.refl_apply]
      apply Finset.mem_image.mpr
      refine ⟨⟨j.val,by omega⟩,Finset.mem_univ _,?_⟩
      exact hj
    · have hjd':j.val=d:=by omega
      have heq:a=(π^d).symm x:=by
        have hone:((1:Equiv.Perm V).symm) a=a:=by rfl
        have hx':(π^d) a=x:=by simpa only [hjd',hone] using hj
        exact ((π^d).apply_eq_iff_eq_symm_apply).mp hx'
      apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _,by simpa only [←heq] using ha⟩
  have hc: A.card≤B.card+C.card:=(Finset.card_le_card hsub).trans (Finset.card_union_le B C)
  have hcR:(A.card:ℝ)≤(B.card:ℝ)+C.card:=by exact_mod_cast hc
  have hB:(B.card:ℝ)=rawIntervalAssignedLabelColumnCount π d σ x g Finset.univ:=by
    simp [B,rawIntervalAssignedLabelColumnCount,Finset.sum_ite]
  have hC:(C.card:ℝ)=rawIntervalStartColumnCount π d σ ((π^d).symm x) g Finset.univ:=by
    simp [C,rawIntervalStartColumnCount,Finset.sum_ite]
  simpa only [hB,hC] using hcR
end Oberwolfach
