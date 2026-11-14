module

public import Oberwolfach.OrientationDisagreementGraph
public import Oberwolfach.Neighbourhoods

@[expose] public section
/-! A correction graph relative to the sampled class has small degree when
the class graph and its final direction differ by bounded amounts. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem class_orientation_correction_degree
    {V:Type} [Fintype V] [LinearOrder V] (S₀ S:SimpleGraph V) (bits:Sym2 V→Bool)
    (M:V→V→ℕ) (v:V):
    ((orientationDisagreementGraph S₀ bits M).degree v:ℝ)≤
      ((changed (S₀.neighborFinset v) (S.neighborFinset v)).card:ℝ)+
      ((Finset.univ.filter (fun w=>M v w≠sampledOrientation S bits v w ∨
        M w v≠sampledOrientation S bits w v)).card:ℝ):=by
  let A:=changed (S₀.neighborFinset v) (S.neighborFinset v)
  let B:=Finset.univ.filter (fun w=>M v w≠sampledOrientation S bits v w ∨
    M w v≠sampledOrientation S bits w v)
  have hsub:(orientationDisagreementGraph S₀ bits M).neighborFinset v⊆A∪B:=by
    intro w hw
    have h:=(SimpleGraph.mem_neighborFinset _ _ _).mp hw
    by_cases hS:S.Adj v w
    · by_cases hB:M v w≠sampledOrientation S bits v w ∨ M w v≠sampledOrientation S bits w v
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hB⟩)
      · have hEq1:sampledOrientation S bits v w=sampledOrientation S₀ bits v w:=by
          simp [sampledOrientation,hS,h.1]
        have hEq2:sampledOrientation S bits w v=sampledOrientation S₀ bits w v:=by
          simp [sampledOrientation,hS.symm,h.1.symm]
        have hnot:¬(M v w≠sampledOrientation S₀ bits v w ∨ M w v≠sampledOrientation S₀ bits w v):=by
          rw [←hEq1,←hEq2]
          exact hB
        exact False.elim (hnot h.2)
    · apply Finset.mem_union_left
      simp [A,changed,SimpleGraph.mem_neighborFinset,h.1,hS]
  have hc:(orientationDisagreementGraph S₀ bits M).degree v≤A.card+B.card:=by
    exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hc':((orientationDisagreementGraph S₀ bits M).degree v:ℝ)≤(A.card:ℝ)+B.card:=by exact_mod_cast hc
  exact hc'
end Oberwolfach
