module

public import Oberwolfach.OrdinaryFreshLocalFactor
public import Oberwolfach.OrdinaryLocalAugmentWeights
public import Oberwolfach.OrdinaryLocalFactorHostTransfer

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

theorem ordinary_fresh_factor_inside_roots_general (m:ℕ) (hm:2≤m) (γ κ b B:ℝ)
    (hγ:0<γ) (hκ:0<κ) (hb:0<b) (hB:0≤B):
    ∃ε η ζ:ℝ,0<ε∧0<η∧0<ζ∧
    ∀(p:ℝ) (hp:0<p) (hp1:p≤1) (q:ℕ),∃N:ℕ,
    ∀(V:Type) [Fintype V] [DecidableEq V],N≤Fintype.card V→
    ∀(Q F:SimpleGraph V) (T:Finset V),κ*Fintype.card V≤(T.card:ℝ)→
    (∀v,(F.degree v:ℝ)≤ε*Fintype.card V)→
    (∀S:Finset V,S⊆T→S.card≤(if m=2 then 3 else 2)→γ*Fintype.card V≤((common T S (fun x=>Q.neighborFinset x)).card:ℝ))→
    ∀wt:LocalOrdinaryCycle Q F T (m+1)→ℝ,
    (∀C,b/(Fintype.card V:ℝ)^m≤wt C∧wt C≤B/(Fintype.card V:ℝ)^m)→
    (∀v∈T,|1-hypergraphWeightedDegree localOrdinaryVertices wt v|≤η)→
    1-1/(T.card:ℝ)^q≤(FiniteLaw.pi (fun _:V=>FiniteLaw.retentionCoin p hp.le hp1)).probability
      (fun σ=>∀Y:Finset V,Y⊆T→(m+1)∣Y.card→
        ((((T∩bernoulliVertexSet σ)\Y).card+(Y\(T∩bernoulliVertexSet σ)).card:ℕ):ℝ)≤ζ*(p*T.card)→
        ∀K:SimpleGraph V,(∀v,(K.degree v:ℝ)≤ζ*(p*T.card))→
        ∃D:Finset (LocalOrdinaryCycle Q F T (m+1)),
          ((∀C∈D,∀E∈D,C≠E→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices E)) ∧
            D.biUnion localOrdinaryVertices=Y) ∧
          ∀C∈D,∀x∈localOrdinaryVertices C,∀y∈localOrdinaryVertices C,¬K.Adj x y):=by
  obtain ⟨ε,η,ζ,hε,hη,hζ,hbase⟩:=ordinary_fresh_local_factor m hm γ κ b B hγ hκ hb hB
  refine ⟨ε,η,ζ,hε,hη,hζ,?_⟩
  intro p hp hp1 q
  obtain ⟨N,hN⟩:=hbase p hp hp1 q
  refine ⟨N,?_⟩
  intro V _ _ hn Q F T hsize hF hcommon wt hw hload
  let Qa:=ordinaryLocalHostAugment Q T
  let e:=ordinaryLocalAugmentEquiv (r:=m+1) Q F T
  let wa:LocalOrdinaryCycle Qa F T (m+1)→ℝ:=fun C=>wt (e.symm C)
  have hcommonA:∀S:Finset V,S.card≤(if m=2 then 3 else 2)→γ*Fintype.card V≤
      ((common T S (fun x=>Qa.neighborFinset x)).card:ℝ):=by
    intro S hS
    rw [ordinary_local_host_augment_common]
    exact hcommon (S∩T) Finset.inter_subset_right ((Finset.card_le_card Finset.inter_subset_left).trans hS)
  have hwa:∀C,b/(Fintype.card V:ℝ)^m≤wa C∧wa C≤B/(Fintype.card V:ℝ)^m:=fun C=>hw (e.symm C)
  have hla:∀v∈T,|1-hypergraphWeightedDegree localOrdinaryVertices wa v|≤η:=by
    intro v hv
    have hh:=ordinary_local_augment_weighted_degree Q F T wt v
    rw [hh]
    exact hload v hv
  have hh:=hN V hn Qa F T hsize hF hcommonA wa hwa hla
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ Y hYT hdiv hchange K hK
  obtain ⟨D,hD,havoid⟩:=hσ Y hYT hdiv hchange K hK
  let D':=D.image e.symm
  have hvertices (C:LocalOrdinaryCycle Qa F T (m+1)):
      localOrdinaryVertices (e.symm C)=localOrdinaryVertices C:=by rfl
  have hpair:∀C∈D',∀E∈D',C≠E→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices E):=by
    intro C hC E hE hne
    obtain ⟨c,hc0,rfl⟩:=Finset.mem_image.mp hC
    obtain ⟨e₀,he0,rfl⟩:=Finset.mem_image.mp hE
    rw [hvertices,hvertices]
    exact hD.1 c hc0 e₀ he0 (fun h=>hne (by rw [h]))
  have hcover:D'.biUnion localOrdinaryVertices=Y:=by
    rw [←hD.2]
    ext x
    simp only [D',Finset.mem_biUnion,Finset.mem_image]
    constructor
    · rintro ⟨C,⟨C₀,hC₀,rfl⟩,hx⟩
      exact ⟨C₀,hC₀,by simpa only [hvertices] using hx⟩
    · rintro ⟨C,hC,hx⟩
      exact ⟨e.symm C,⟨C,hC,rfl⟩,by simpa only [hvertices] using hx⟩
  refine ⟨D',⟨hpair,hcover⟩,?_⟩
  intro C hC x hx y hy
  obtain ⟨c,hc0,rfl⟩:=Finset.mem_image.mp hC
  rw [hvertices] at hx hy
  exact havoid c hc0 x hx y hy
end Oberwolfach
