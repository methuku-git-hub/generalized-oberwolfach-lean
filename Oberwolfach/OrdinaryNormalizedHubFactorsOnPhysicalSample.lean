module

public import Oberwolfach.OrdinaryHubFactorNormalizedInputs
public import Oberwolfach.OrdinaryFreshNormalizedDomainFamily
public import Oberwolfach.OrdinaryBoundaryRootSets
public import Oberwolfach.MarkedFreshHubCommonEvent

@[expose] public section
/-! Apply the normalized factor theorem on the actual hub classes using
the same ambient physical-edge coins. The local graph inputs can be
selected after the earlier sample, before these fresh coins are exposed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def OrdinaryNormalizedHubFactorEvent (m:ℕ) (Q F:SimpleGraph V) (H:V→U→Prop)
    (A:Finset V) (Z:Finset U) (p ζ:ℝ) (σ:Sym2 (V⊕U)→Bool):Prop:=
  ∀j:{u:U // u∉Z},
    let T:=ordinaryBoundaryHubSet H Z A j
    ∀Y:Finset {v:V // v∈T},(m+1)∣Y.card→
      ((((Finset.univ∩bernoulliVertexSet (fun v=>σ (hubSpokeCoin j.val v.val)))\Y).card+
        (Y\(Finset.univ∩bernoulliVertexSet (fun v=>σ (hubSpokeCoin j.val v.val)))).card:ℕ):ℝ)≤
          ζ*(p*Fintype.card {v:V // v∈T})→
      ∀K:SimpleGraph {v:V // v∈T},(∀v,(K.degree v:ℝ)≤ζ*(p*Fintype.card {v:V // v∈T}))→
      ∃D:Finset (LocalOrdinaryCycle ((spanningRestriction Q A).induce (T:Set V))
        (F.induce (T:Set V)) Finset.univ (m+1)),
        ((∀C∈D,∀C'∈D,C≠C'→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices C')) ∧
          D.biUnion localOrdinaryVertices=Y) ∧
        ∀C∈D,∀x∈localOrdinaryVertices C,∀y∈localOrdinaryVertices C,¬K.Adj x y

theorem ordinary_normalized_hub_factors_on_physical_sample
    (m:ℕ) (hm:2≤m) (γ b B:ℝ) (hγ:0<γ) (hb:0<b) (hB:0≤B):
    ∃ε η ζ:ℝ,0<ε ∧ 0<η ∧ 0<ζ ∧ ∀(p:ℝ) (hp:0<p) (hp1:p≤1) (q:ℕ),∃N:ℕ,
    ∀(V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
      (Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (Z:Finset U),
    N≤A.card→0<A.card→Fintype.card {u:U // u∉Z}≤A.card^2→
    (∀j:{u:U // u∉Z},γ*A.card≤((ordinaryBoundaryHubSet H Z A j).card:ℝ))→
    (∀j:{u:U // u∉Z},∀S:Finset V,S⊆ordinaryBoundaryHubSet H Z A j→
      S.card≤(if m=2 then 3 else 2)→γ*A.card≤((common (ordinaryBoundaryHubSet H Z A j) S
        (fun x=>(spanningRestriction Q A).neighborFinset x)).card:ℝ))→
    (∀j:{u:U // u∉Z},∀v:{v:V // v∈ordinaryBoundaryHubSet H Z A j},
      ((F.induce ((ordinaryBoundaryHubSet H Z A j):Set V)).degree v:ℝ)≤
        ε*Fintype.card {v:V // v∈ordinaryBoundaryHubSet H Z A j})→
    OrdinaryMixedHubWeightsInnerScale m b B η Q F H A Z→
    1-1/(A.card:ℝ)^q≤
      (FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1)).probability
        (OrdinaryNormalizedHubFactorEvent m Q F H A Z p ζ):=by
  have hbg:0<b*γ^m:=mul_pos hb (pow_pos hγ _)
  obtain ⟨ε,η,ζ,hε,hη,hζ,hfamily⟩:=ordinary_fresh_normalized_domain_family m hm γ γ (b*γ^m) B hγ hγ hbg hB
  refine ⟨ε,η,ζ,hε,hη,hζ,?_⟩
  intro p hp hp1 q
  obtain ⟨N,hN⟩:=hfamily p hp hp1 q
  refine ⟨N,?_⟩
  intro V U _ _ _ _ Q F H A Z hn hA hJ hsize hcommon hF data
  let J:Type:={u:U // u∉Z}
  let T:J→Finset V:=fun j=>ordinaryBoundaryHubSet H Z A j
  let D:J→Type:=fun j=>{v:V // v∈T j}
  let f:∀j,D j↪Sym2 (V⊕U):=fun j=>(Function.Embedding.subtype (fun v:V=>v∈T j)).trans (hubSpokeCoin j.val)
  let Qj:∀j,SimpleGraph (D j):=fun j=>(spanningRestriction Q A).induce (T j:Set V)
  let Fj:∀j,SimpleGraph (D j):=fun j=>F.induce (T j:Set V)
  have hi:=ordinary_hub_factor_normalized_inputs m (if m=2 then 3 else 2) b B η γ Q F H A Z
    hA hb.le hB hγ hsize hcommon data
  choose wt hwt hload using fun j:J=>(hi j).2
  have hs:∀j:J,γ*A.card≤(Fintype.card (D j):ℝ):=by
    intro j
    simpa [D,T] using hsize j
  have hc:∀j:J,∀S:Finset (D j),S.card≤(if m=2 then 3 else 2)→
      γ*Fintype.card (D j)≤((common Finset.univ S (fun x=>(Qj j).neighborFinset x)).card:ℝ):=by
    intro j S hS
    exact (hi j).1 S hS
  have hf:∀j v,((Fj j).degree v:ℝ)≤ε*Fintype.card (D j):=hF
  have hprob:=hN A.card hn J (Sym2 (V⊕U)) D hJ hs f Qj Fj hf hc wt hwt hload
  exact hprob
end Oberwolfach
