module

public import Oberwolfach.EdgeRetention
public import Oberwolfach.CommonEvents

@[expose] public section
/-! Simultaneous retained-degree concentration for the physical class graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem retained_graph_degree_concentration {V:Type} [Fintype V] [DecidableEq V]
    (P:SimpleGraph V) (ρ t:ℝ) (hρ:0≤ρ) (hρ1:ρ≤1) (ht:0≤t):
    1-2*(Fintype.card V:ℝ)*Real.exp (-2*t^2/Fintype.card V)≤
      (FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.retentionCoin ρ hρ hρ1)).probability
        (fun σ=>∀v,|((retainedGraph P σ).degree v:ℝ)-ρ*(P.degree v:ℝ)|<t) :=by
  let μ:=FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.retentionCoin ρ hρ hρ1)
  let Bad:=fun (v:V) (σ:Sym2 V→Bool)=>t≤|((retainedGraph P σ).degree v:ℝ)-ρ*(P.degree v:ℝ)|
  have hEach:∀v:V,μ.probability (Bad v)≤2*Real.exp (-2*t^2/Fintype.card V):=by
    intro v
    have hh:=retained_neighbour_count_tail P (Finset.univ:Finset V)
      (fun _:Sym2 V=>FiniteLaw.retentionCoin ρ hρ hρ1) v t ht
    have hevent:(fun σ:Sym2 V→Bool=>t≤|(retainedNeighbourCount P Finset.univ σ v:ℝ)-
        ∑x∈P.neighborFinset v∩Finset.univ,(FiniteLaw.retentionCoin ρ hρ hρ1).mass true|)=Bad v:=by
      funext σ
      apply propext
      simp only [retainedNeighbourCount_eq,Finset.inter_univ,SimpleGraph.card_neighborFinset_eq_degree,
        FiniteLaw.retentionCoin,Bool.true_eq,ite_true,Finset.sum_const,nsmul_eq_mul]
      simp only [Bad,mul_comm]
    rw [hevent] at hh
    simpa only [μ,Finset.card_univ] using hh
  have hh:=finiteLaw_common_event_lower μ (Finset.univ:Finset V) Bad
    (fun _=>2*Real.exp (-2*t^2/Fintype.card V)) (fun v _=>hEach v)
  have hs:(∑_v:V,2*Real.exp (-2*t^2/Fintype.card V))=
      2*(Fintype.card V:ℝ)*Real.exp (-2*t^2/Fintype.card V):=by simp;ring
  rw [hs] at hh
  apply hh.trans
  apply finiteLaw_probability_mono μ _ _
  intro σ hσ v
  have h:=hσ v (Finset.mem_univ v)
  exact lt_of_not_ge h
end Oberwolfach
