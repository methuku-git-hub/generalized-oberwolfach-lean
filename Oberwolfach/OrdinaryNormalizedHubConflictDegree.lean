module

public import Oberwolfach.OrdinaryBoundaryRootSets

@[expose] public section
/-! A bounded ambient conflict degree remains bounded after induction onto
each actual hub class; its fixed cost is absorbed by the class size. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_induced_degree_le (F:SimpleGraph V) (T:Finset V) (v:{v:V // v∈T}):
    (F.induce (T:Set V)).degree v≤F.degree v.val:=by
  have hs:((F.induce (T:Set V)).neighborFinset v).map
      (Function.Embedding.subtype (fun v:V=>v∈(T:Set V)))⊆F.neighborFinset v.val:=by
    intro x hx
    obtain ⟨y,hy,rfl⟩:=Finset.mem_map.mp hx
    change y.val∈F.neighborFinset v.val
    simpa only [SimpleGraph.mem_neighborFinset,SimpleGraph.induce_adj] using hy
  have hc:=Finset.card_le_card hs
  simpa only [Finset.card_map,SimpleGraph.card_neighborFinset_eq_degree] using hc

theorem ordinary_normalized_hub_conflict_degree
    (F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (Z:Finset U) (γ ε L:ℝ)
    (hε:0≤ε) (hF:∀v,(F.degree v:ℝ)≤L) (hsmall:L≤ε*(γ*A.card))
    (hsize:∀j:{u:U // u∉Z},γ*A.card≤((ordinaryBoundaryHubSet H Z A j).card:ℝ)):
    ∀j:{u:U // u∉Z},∀v:{v:V // v∈ordinaryBoundaryHubSet H Z A j},
      ((F.induce ((ordinaryBoundaryHubSet H Z A j):Set V)).degree v:ℝ)≤
        ε*Fintype.card {v:V // v∈ordinaryBoundaryHubSet H Z A j}:=by
  intro j v
  have hdeg:((F.induce ((ordinaryBoundaryHubSet H Z A j):Set V)).degree v:ℝ)≤F.degree v.val:=by
    exact_mod_cast ordinary_induced_degree_le F (ordinaryBoundaryHubSet H Z A j) v
  have hh:=mul_le_mul_of_nonneg_left (hsize j) hε
  simpa using hdeg.trans ((hF v.val).trans (hsmall.trans hh))
end Oberwolfach
