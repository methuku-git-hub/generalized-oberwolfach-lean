module

public import Oberwolfach.ClassInsertionBudget
public import Oberwolfach.ClassResidualGraphContainment

@[expose] public section
/-! Regularising the class adds only the actual edit degree to the precise
sampled required-graph bound. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem class_required_precise_degree_from_edits
    {n:ℕ} (P S₀ S Used Sel:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (I:Finset (Fin n)) (D:Fin n→Fin n→Prop) (θ lam ξ t:ℝ)
    (hSP:S≤P)
    (hedit:∀v,((changed (S₀.neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*n)
    (hdegree:∀v,((longRequiredPhysicalGraph P (S₀\Used) Sel π d I D
      (fun x y=>Used.Adj x y)).degree v:ℝ)≤2*θ*I.card+t+lam*n+(6*d+2:ℕ)):
    ∀v,((longRequiredPhysicalGraph S (S\Used) Sel π d I D
      (fun x y=>Used.Adj x y)).degree v:ℝ)≤2*θ*I.card+t+(lam+ξ)*n+(6*d+2:ℕ) :=by
  let K:=longRequiredPhysicalGraph S (S\Used) Sel π d I D (fun x y=>Used.Adj x y)
  let K₀:=longRequiredPhysicalGraph P (S₀\Used) Sel π d I D (fun x y=>Used.Adj x y)
  let E:=spanningRestriction (S\S₀) I
  have hsub:=class_required_graph_edit_bounds P S₀ S Used Sel π d I D hSP
  have hbudget:=class_insertion_edge_budget S₀ S I (ξ*n) hedit
  intro v
  have hh:(K.degree v:ℝ)≤(K₀.degree v:ℝ)+(E.degree v:ℝ):=by exact_mod_cast hsub.1 v
  have he:=hbudget.1 v
  have hk:=hdegree v
  dsimp only [K,K₀,E] at *
  linarith
end Oberwolfach
