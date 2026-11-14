module

public import Oberwolfach.LongThreeGraphDegree
public import Oberwolfach.LongPreparationIneligibleGraph

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_ineligible_union_degree_budget
    {n d:ℕ} (G Del Loss:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (δDel δLoss:ℝ)
    (hDel:∀v,(Del.degree v:ℝ)≤δDel*n) (hLoss:∀v,(Loss.degree v:ℝ)≤δLoss*n):
    ∀v,((Del⊔Loss⊔longPreparationIneligibleGraph G π d).degree v:ℝ)≤(δDel+δLoss)*n+(6*d+2:ℕ):=by
  intro v
  let Bad:=longPreparationIneligibleGraph G π d
  have hd:=long_three_graph_degree_bound Del Loss Bad v
  have hi:=long_preparation_ineligible_degree G π d v
  have hDelv:=hDel v
  have hLossv:=hLoss v
  simp only [← SimpleGraph.ncard_neighborSet] at hd hi hDelv hLossv ⊢
  have hdr:(((Del⊔Loss⊔Bad).neighborSet v).ncard:ℝ)≤
    (Del.neighborSet v).ncard+(Loss.neighborSet v).ncard+(Bad.neighborSet v).ncard:=by exact_mod_cast hd
  have hir:((Bad.neighborSet v).ncard:ℝ)≤(6*d+2:ℕ):=by exact_mod_cast hi
  linarith only [hdr,hir,hDelv,hLossv]
end Oberwolfach
