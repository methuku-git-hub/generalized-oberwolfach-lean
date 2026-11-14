module

public import Oberwolfach.OrdinarySameSampleBalanceProfiles
public import Oberwolfach.OrdinaryProtectedBoundaryEdit

@[expose] public section
/-! The original row tests and the exact regular-host mean give the global
near-balance required by sparse correction after forbidden edges are removed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_global_balance_from_sample
    (P F:SimpleGraph V) (D:ℕ) (hreg:P.IsRegularOfDegree D)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (σ:RawWheelOutcome V U Γ Color)
    (pR pH tR tH L η:ℝ) (s:U→Color→ℝ)
    (htR:0≤tR) (htH:0≤tH) (hL:0≤L)
    (hmean:pR*D=2*pH*Fintype.card U)
    (hrows:RawOrdinaryRows P π d 2 Finset.univ pR s j tR σ)
    (hcols:RawOrdinaryDomainIndices F π d 3 Finset.univ pH j tH σ)
    (hF:∀v,(F.degree v:ℝ)≤L) (hbudget:tR+2*tH+3*L≤η*Fintype.card V):
    ∀v,|(((rawWheelGraph P σ)\F).degree v:ℝ)-
      2*(Finset.univ.filter (rawWheelSpokes π d σ j v)).card|≤η*Fintype.card V:=by
  have hparent:∀v,|pR*(P.neighborFinset v∩Finset.univ).card-2*pH*(Finset.univ:Finset U).card|≤(0:ℝ):=by
    intro v
    simp only [Finset.inter_univ,SimpleGraph.card_neighborFinset_eq_degree,Finset.card_univ,hreg v,hmean,sub_self,abs_zero,le_refl]
  have hrim:∀v,((changed (((rawWheelGraph P σ)\F).neighborFinset v) ((rawWheelGraph P σ).neighborFinset v)).card:ℝ)≤L:=by
    intro v
    have hh:((changed ((rawWheelGraph P σ).neighborFinset v) (((rawWheelGraph P σ)\F).neighborFinset v)).card:ℝ)≤L:=
      (Nat.cast_le.mpr (graph_changed_neighbors_after_deletion (rawWheelGraph P σ) F v)).trans (hF v)
    simpa only [changed,Finset.union_comm] using hh
  have hspoke:∀v,((changed (Finset.univ.filter (rawWheelSpokes π d σ j v))
      (Finset.univ.filter (rawWheelSpokes π d σ j v))).card:ℝ)≤L:=by
    intro v
    simpa [changed,Finset.sdiff_self] using hL
  have h:=ordinary_same_sample_balance_profiles P F ((rawWheelGraph P σ)\F) (rawWheelSpokes π d σ j) π d
    Finset.univ Finset.univ pR pH tR tH 0 L htR htH (by norm_num) hL s j σ hrows hcols hparent
      (by intro v;convert hrim v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) hspoke
  intro v
  have hv:=h.1 v
  simp only [Finset.inter_univ,SimpleGraph.card_neighborFinset_eq_degree,zero_add] at hv
  convert hv.trans hbudget using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
