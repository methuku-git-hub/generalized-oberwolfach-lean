module

public import Oberwolfach.OrdinaryProtectedRequiredDegree

@[expose] public section
/-! Concentration of rim and spoke degrees about matching centres yields the
    balance needed for the sparse correction, even after a bounded conflict
    graph is removed from the reference rim. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_reference_balance_from_degrees
    (G F:SimpleGraph V) (H:V→U→Prop) (μ:V→ℝ) (ν eR eH L:ℝ)
    (hcentre:∀v,μ v=2*ν)
    (hR:∀v,|(G.degree v:ℝ)-μ v|≤eR)
    (hH:∀v,|((Finset.univ.filter (H v)).card:ℝ)-ν|≤eH)
    (hF:∀v,(F.degree v:ℝ)≤L):
    ∀v,|((G\F).degree v:ℝ)-2*((Finset.univ.filter (H v)).card:ℝ)|≤eR+2*eH+L:=by
  intro v
  have hle:((G\F).degree v:ℝ)≤G.degree v:=by
    exact_mod_cast (SimpleGraph.degree_le_of_le (show G\F≤G from sdiff_le) (v:=v))
  have hsub:G≤(G\F)⊔F:=by
    intro x y he
    by_cases hf:F.Adj x y
    · exact Or.inr hf
    · exact Or.inl ⟨he,hf⟩
  have hs:=graph_sup_degree_le (G\F) F v
  have hd:=SimpleGraph.degree_le_of_le hsub (v:=v)
  have hhi:(G.degree v:ℝ)≤((G\F).degree v:ℝ)+F.degree v:=by
    simp only [←SimpleGraph.ncard_neighborSet] at hs hd ⊢
    exact_mod_cast hd.trans hs
  have hRlower: -eR≤(G.degree v:ℝ)-μ v:=(abs_le.mp (hR v)).1
  have hRupper: (G.degree v:ℝ)-μ v≤eR:=(abs_le.mp (hR v)).2
  have hHlower: -eH≤((Finset.univ.filter (H v)).card:ℝ)-ν:=(abs_le.mp (hH v)).1
  have hHupper: ((Finset.univ.filter (H v)).card:ℝ)-ν≤eH:=(abs_le.mp (hH v)).2
  apply abs_le.mpr
  constructor <;> linarith [hcentre v,hF v]
end Oberwolfach
