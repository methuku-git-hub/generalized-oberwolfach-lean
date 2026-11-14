module

public import Oberwolfach.MarkedNeighbourhoodsLocalChange

@[expose] public section
/-! Restrict boundary-row rim changes to a protected inner set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_boundary_rim_local_changes
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (I A:Finset V) (hAI:A⊆I)
    (hπ:∀v,π v∈I↔v∈I)
    (σ τ:RawMarkedOutcome V U Γ Color) (FR:SimpleGraph V) (δ:ℝ) (hδ:0≤δ)
    (hrim:∀mark v w,v∈I→w∈I→
      (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark v w=1 ↔
       markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark v w=1))
    (hchange:∀a,¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a)→markedPairPhysical π a∈FR.edgeFinset)
    (hFR:∀v,v∉I→(FR.degree v:ℝ)≤δ):
    ∀a,(∑x∈A,if ¬(rawMarkedPairRims P π d σ (markedRowRim a x)↔
      rawMarkedPairRims P π d τ (markedRowRim a x)) then (1:ℝ) else 0)≤δ :=by
  intro a
  rcases a with ⟨mark,incoming,v⟩
  by_cases hv:v∈I
  · have hz:(∑x∈A,if ¬(rawMarkedPairRims P π d σ (markedRowRim (mark,incoming,v) x)↔
        rawMarkedPairRims P π d τ (markedRowRim (mark,incoming,v) x)) then (1:ℝ) else 0)=0:=by
      apply Finset.sum_eq_zero
      intro x hx
      have hxI:=hAI hx
      cases mark <;> cases incoming <;>
        simp only [markedRowRim,rawMarkedPairRims,Bool.false_eq_true,ite_false,ite_true,Sum.elim_inl,Sum.elim_inr] <;>
        simp [hrim _ _ _ hv hxI,hrim _ _ _ hxI hv]
    simpa only [hz] using hδ
  · have hroot:(if mark && incoming then π v else v)∉I:=by
      split_ifs with h
      · exact fun hmem=>hv ((hπ v).mp hmem)
      · exact hv
    calc
      _ ≤ ∑x:V,if ¬(rawMarkedPairRims P π d σ (markedRowRim (mark,incoming,v) x)↔
          rawMarkedPairRims P π d τ (markedRowRim (mark,incoming,v) x)) then (1:ℝ) else 0:=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) (by intro x _ _;split_ifs <;> norm_num)
      _ ≤ (FR.degree (if mark && incoming then π v else v):ℝ):=
        marked_row_rim_physical_change P π d σ τ FR hchange mark incoming v
      _ ≤ δ:=hFR _ hroot
end Oberwolfach
