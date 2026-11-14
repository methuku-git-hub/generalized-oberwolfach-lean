module

public import Oberwolfach.ExpandedPhysicalRestrictedDegree
public import Oberwolfach.ColourDegreeLocalScale

@[expose] public section
/-! Concentration in a prescribed set of rows, at the inner set's scale. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [LinearOrder V]

theorem physicalRestrictedColourDegree_local_event
    (G:SimpleGraph V) (A B:Finset V) (ρ:Fin 6→ℝ) (hρ:∀ a,0≤ρ a) (hsum:∑ a,ρ a=1)
    (a:Fin 6) (t:ℝ) (ht:0<t):
    1-2*(B.card:ℝ)*Real.exp (-2*t^2/(A.card:ℝ))≤
      (FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.categoricalDirection ρ hρ hsum)).probability (fun σ=>∀ x∈B,
        |(((G.neighborFinset x∩A).filter (fun y=>(σ s(x,y)).1=a)).card:ℝ)-
          ρ a*(G.neighborFinset x∩A).card|<t):=by
  let μ:=FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.categoricalDirection ρ hρ hsum)
  have hh:=finiteLaw_common_event_lower μ B
    (fun x σ=>t≤|(((G.neighborFinset x∩A).filter (fun y=>(σ s(x,y)).1=a)).card:ℝ)-
      ρ a*(G.neighborFinset x∩A).card|)
    (fun _=>2*Real.exp (-2*t^2/(A.card:ℝ)))
    (fun x _=>by
      have hN : ((physicalRootRestrictedGraph G x A).degree x:ℝ)≤A.card := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree, physicalRootRestrictedGraph_neighbours]
        exact_mod_cast Finset.card_le_card (Finset.inter_subset_right : G.neighborFinset x ∩ A ⊆ A)
      have hx:=sampledColourDegree_joint_tail_at_scale (physicalRootRestrictedGraph G x A) ρ hρ hsum a x A.card hN ht.le
      simp_rw [physicalRootRestrictedGraph_colour_degree, ← SimpleGraph.card_neighborFinset_eq_degree,
        physicalRootRestrictedGraph_neighbours] at hx
      exact hx)
  simp only [Finset.sum_const,nsmul_eq_mul,not_le] at hh
  convert hh using 1 <;> ring
end Oberwolfach
