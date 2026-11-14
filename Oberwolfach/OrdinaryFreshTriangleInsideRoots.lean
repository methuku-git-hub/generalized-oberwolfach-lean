module

public import Oberwolfach.OrdinaryFreshLocalFactor
public import Oberwolfach.OrdinaryLocalAugmentWeights
public import Oberwolfach.OrdinaryLocalFactorHostTransfer
public import Oberwolfach.TriangleSupportEdges

@[expose] public section
/-! A fresh triangle factor only needs common-neighborhood bounds for roots
inside its own domain. The outside completion is auxiliary and the selected
triangles are transferred back to the original host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
set_option synthInstance.maxSize 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_fresh_triangle_factor_inside_roots (γ κ b B:ℝ)
    (hγ:0<γ) (hκ:0<κ) (hb:0<b) (hB:0≤B):
    ∃ε η ζ:ℝ,0<ε∧0<η∧0<ζ∧
    ∀(p:ℝ) (hp:0<p) (hp1:p≤1) (q:ℕ),∃N:ℕ,
    ∀(V:Type) [Fintype V] [DecidableEq V],N≤Fintype.card V→
    ∀(Q F:SimpleGraph V) (T:Finset V),κ*Fintype.card V≤(T.card:ℝ)→
    (∀v,(F.degree v:ℝ)≤ε*Fintype.card V)→
    (∀S:Finset V,S⊆T→S.card≤3→γ*Fintype.card V≤((common T S (fun x=>Q.neighborFinset x)).card:ℝ))→
    ∀wt:LocalOrdinaryCycle Q F T 3→ℝ,
    (∀C,b/(Fintype.card V:ℝ)^2≤wt C∧wt C≤B/(Fintype.card V:ℝ)^2)→
    (∀v∈T,|1-hypergraphWeightedDegree localOrdinaryVertices wt v|≤η)→
    1-1/(T.card:ℝ)^q≤(FiniteLaw.pi (fun _:V=>FiniteLaw.retentionCoin p hp.le hp1)).probability
      (fun σ=>∀Y:Finset V,Y⊆T→3∣Y.card→
        ((((T∩bernoulliVertexSet σ)\Y).card+(Y\(T∩bernoulliVertexSet σ)).card:ℕ):ℝ)≤ζ*(p*T.card)→
        ∀K:SimpleGraph V,(∀v,(K.degree v:ℝ)≤ζ*(p*T.card))→
        ∃D:Finset (LocalOrdinaryCycle Q F T 3),
          ((∀C∈D,∀E∈D,C≠E→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices E)) ∧
            D.biUnion localOrdinaryVertices=Y) ∧
          ∀C∈D,∀x∈localOrdinaryVertices C,∀y∈localOrdinaryVertices C,¬K.Adj x y):=by
  obtain ⟨ε,η,ζ,hε,hη,hζ,hbase⟩:=ordinary_fresh_local_factor 2 le_rfl γ κ b B hγ hκ hb hB
  refine ⟨ε,η,ζ,hε,hη,hζ,?_⟩
  intro p hp hp1 q
  obtain ⟨N,hN⟩:=hbase p hp hp1 q
  refine ⟨N,?_⟩
  intro V _ _ hn Q F T hsize hF hcommon wt hw hload
  let Qa:=ordinaryLocalHostAugment Q T
  let e:=ordinaryLocalAugmentEquiv (r:=3) Q F T
  let wa:LocalOrdinaryCycle Qa F T 3→ℝ:=fun C=>wt (e.symm C)
  have hcommonA:∀S:Finset V,S.card≤3→γ*Fintype.card V≤
      ((common T S (fun x=>Qa.neighborFinset x)).card:ℝ):=by
    intro S hS
    rw [ordinary_local_host_augment_common]
    exact hcommon (S∩T) Finset.inter_subset_right ((Finset.card_le_card Finset.inter_subset_left).trans hS)
  have hwa:∀C,b/(Fintype.card V:ℝ)^2≤wa C∧wa C≤B/(Fintype.card V:ℝ)^2:=fun C=>hw (e.symm C)
  have hla:∀v∈T,|1-hypergraphWeightedDegree localOrdinaryVertices wa v|≤η:=by
    intro v hv
    have hh:=ordinary_local_augment_weighted_degree Q F T wt v
    rw [hh]
    exact hload v hv
  have hh:=hN V hn Qa F T hsize hF (by simpa only [ite_true] using hcommonA) wa hwa hla
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ Y hYT hdiv hchange K hK
  obtain ⟨D,hD,havoid⟩:=hσ Y hYT hdiv hchange K hK
  have hgraph:localOrdinaryFactorGraph D≤Q:=by
    intro x y hxy
    obtain ⟨C,hC,hCxy⟩:=(localOrdinaryFactorGraph_adj D x y).mp hxy
    exact ordinary_local_augmented_cycle_le Q F T C hCxy
  have hdisK:Disjoint (localOrdinaryFactorGraph D) K:=localOrdinaryFactorGraph_disjoint D K havoid
  obtain ⟨D',hpair,hcover,heq⟩:=local_ordinary_factor_transfer_to_host Qa Q F T 3 D hgraph
  have hdisK':Disjoint (localOrdinaryFactorGraph D') K:=by rw [heq];exact hdisK
  refine ⟨D',⟨hpair.mpr hD.1,hcover.trans hD.2⟩,?_⟩
  intro C hC x hx y hy hKxy
  by_cases hxy:x=y
  · subst y
    exact K.loopless.irrefl x hKxy
  · have hCxy:C.val.val.val.Adj x y:=(C.val.val.property.triangle_adj x y).mpr
      ⟨Set.mem_toFinset.mp hx,Set.mem_toFinset.mp hy,hxy⟩
    exact (disjoint_iff_inf_le.mp hdisK') (v:=x) (w:=y) ⟨(localOrdinaryFactorGraph_adj D' x y).mpr ⟨C,hC,hCxy⟩,hKxy⟩
end Oberwolfach
