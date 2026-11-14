module

public import Oberwolfach.ClassInsertionBudget
public import Oberwolfach.ClassResidualGraphContainment

@[expose] public section
/-! Degree and edge budgets for the actual class required graph, using the
sampled graph with room for the regularisation insertions. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem class_required_budgets_from_edits
    {n:ℕ} (P S₀ S Used Sel:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (I:Finset (Fin n)) (D:Fin n→Fin n→Prop) (α θ ε lam₀ lam b:ℝ)
    (hSP:S≤P) (hedit:∀v,((changed (S₀.neighborFinset v) (S.neighborFinset v)).card:ℝ)≤b*n)
    (hbdeg:b≤α/32) (hbedges:b/2≤(lam-lam₀)*ε)
    (hdegree:∀v,((longRequiredPhysicalGraph P (S₀\Used) Sel π d I D
      (fun x y=>Used.Adj x y)).degree v:ℝ)≤(α/32)*n)
    (hedges:((longRequiredPhysicalGraph P (S₀\Used) Sel π d I D
      (fun x y=>Used.Adj x y)).edgeFinset.card:ℝ)≤
        (θ*ε^2+lam₀*ε)*(n:ℝ)^2+24*d*n)
    (hJ:∀v,((spanningRestriction (P\Used) I\
      longRequiredPhysicalGraph P (S₀\Used) Sel π d I D (fun x y=>Used.Adj x y)).degree v:ℝ)≤ε*n):
    let K:=longRequiredPhysicalGraph S (S\Used) Sel π d I D (fun x y=>Used.Adj x y)
    let J:=spanningRestriction (S\Used) I\K
    (∀v,(K.degree v:ℝ)≤(α/16)*n) ∧
      (K.edgeFinset.card:ℝ)≤(θ*ε^2+lam*ε)*(n:ℝ)^2+24*d*n ∧
      (∀v,(J.degree v:ℝ)≤ε*n):=by
  intro K J
  let K₀:=longRequiredPhysicalGraph P (S₀\Used) Sel π d I D (fun x y=>Used.Adj x y)
  let E:=spanningRestriction (S\S₀) I
  have hsub:=class_required_graph_edit_bounds P S₀ S Used Sel π d I D hSP
  have hbudget:=class_insertion_edge_budget S₀ S I (b*n) hedit
  have hn:0≤(n:ℝ):=Nat.cast_nonneg n
  refine ⟨?_,?_,?_⟩
  · intro v
    have hh:(K.degree v:ℝ)≤(K₀.degree v:ℝ)+(E.degree v:ℝ):=by exact_mod_cast hsub.1 v
    have he:=hbudget.1 v
    have hb:=mul_le_mul_of_nonneg_right hbdeg hn
    dsimp [K₀,E] at *
    linarith [hdegree v]
  · have hh:(K.edgeFinset.card:ℝ)≤(K₀.edgeFinset.card:ℝ)+(E.edgeFinset.card:ℝ):=by exact_mod_cast hsub.2
    have he:=hbudget.2
    have hb:=mul_le_mul_of_nonneg_right hbedges (sq_nonneg (n:ℝ))
    simp only [Fintype.card_fin] at he
    dsimp [K₀,E] at *
    nlinarith
  · intro v
    have hle:=class_residual_graph_le_sampled P S₀ S Used Sel π d I D hSP
    have hd: J.degree v≤(spanningRestriction (P\Used) I\K₀).degree v:=by
      apply Finset.card_le_card
      intro w hw
      exact (SimpleGraph.mem_neighborFinset _ _ _).mpr (hle ((SimpleGraph.mem_neighborFinset _ _ _).mp hw))
    have hd':(J.degree v:ℝ)≤((spanningRestriction (P\Used) I\K₀).degree v:ℝ):=by exact_mod_cast hd
    exact hd'.trans (hJ v)
end Oberwolfach
