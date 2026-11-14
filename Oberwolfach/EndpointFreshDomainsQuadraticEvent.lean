module

public import Oberwolfach.EndpointTriangleFreshFactor
public import Oberwolfach.EndpointFactorGraphChoice
public import Oberwolfach.FixedDomainQuadraticEvent
public import Oberwolfach.FiniteProductProjection

@[expose] public section

/-! One physical-coordinate event supplies every endpoint triangle factor,
including all subsequent altered classes with the exact final ratio and all
subsequent forbidden graphs within the stated degree bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 6500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem endpoint_fresh_domains_quadratic_event (γ b B:ℝ) (hγ:0<γ) (hb:0<b) (hB:0≤B):
    ∃ ε η ζ:ℝ,0<ε ∧ 0<η ∧ 0<ζ ∧ ∀ (p:ℝ) (hp:0<p) (hp1:p≤1) (q:ℕ),∃ N:ℕ,
      ∀ (V J E:Type) [Fintype V] [DecidableEq V] [Fintype J] [Fintype E] [DecidableEq E],
      N≤Fintype.card V→Fintype.card J≤(Fintype.card V)^2→
      ∀ (Q F:SimpleGraph V) (S T:J→Finset V) (f:J→V↪E) (hST:∀ j,Disjoint (S j) (T j)),
      (∀ v,(F.degree v:ℝ)≤ε*Fintype.card V)→
      (∀ j,EndpointNeighbourCounts Q F (S j) (T j) (γ*Fintype.card V))→
      ∀ wt:∀ j,EndpointTriangle Q F (S j) (T j)→ℝ,
      (∀ j C,b/(Fintype.card V:ℝ)^2≤wt j C ∧ wt j C≤B/(Fintype.card V:ℝ)^2)→
      (∀ j,∀ v∈S j∪T j,|1-hypergraphWeightedDegree endpointTriangleVertices (wt j) v|≤η)→
      1-1/(Fintype.card V:ℝ)^q≤
        (FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp.le hp1)).probability
          (fun σ=>∀ j,∀ Y:Finset V,Y⊆S j∪T j→(Y∩S j).card=2*(Y∩T j).card→
            (((((S j∪T j).filter (fun v=>σ (f j v)=true))\Y).card+
              (Y\((S j∪T j).filter (fun v=>σ (f j v)=true))).card:ℕ):ℝ)≤ζ*(p*(T j).card)→
            ∀ K:SimpleGraph V,(∀ v,(K.degree v:ℝ)≤ζ*(p*(T j).card))→
            ∃ D:Finset (EndpointTriangle Q F (S j) (T j)),
              ((∀ C∈D,∀ E∈D,C≠E→Disjoint (endpointTriangleVertices C) (endpointTriangleVertices E)) ∧
                D.biUnion endpointTriangleVertices=Y) ∧
              endpointFactorGraph (hST j) D≤spanningRestriction Q Y ∧
              (∀ v,(endpointFactorGraph (hST j) D).degree v≤2) ∧
              Disjoint (endpointFactorGraph (hST j) D) K):=by
  obtain ⟨ε,η,ζ,hε,hη,hζ,hbase⟩:=endpoint_triangle_fresh_factor γ b B hγ hb hB
  refine ⟨ε,η,ζ,hε,hη,hζ,?_⟩
  intro p hp hp1 q
  obtain ⟨Nf,hNf⟩:=hbase p hp hp1 (q+3)
  obtain ⟨Nc,hNc⟩:=fixed_domain_quadratic_common_event γ hγ q
  refine ⟨max Nf Nc,?_⟩
  intro V J E _ _ _ _ _ hn hJ Q F S T f hST hF hcommon wt hw herr
  let μ:=FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp.le hp1)
  let A:J→(E→Bool)→Prop:=fun j σ=>∀ Y:Finset V,Y⊆S j∪T j→(Y∩S j).card=2*(Y∩T j).card→
    (((((S j∪T j).filter (fun v=>σ (f j v)=true))\Y).card+
      (Y\((S j∪T j).filter (fun v=>σ (f j v)=true))).card:ℕ):ℝ)≤ζ*(p*(T j).card)→
    ∀ K:SimpleGraph V,(∀ v,(K.degree v:ℝ)≤ζ*(p*(T j).card))→
    ∃ D:Finset (EndpointTriangle Q F (S j) (T j)),
      ((∀ C∈D,∀ E∈D,C≠E→Disjoint (endpointTriangleVertices C) (endpointTriangleVertices E)) ∧
        D.biUnion endpointTriangleVertices=Y) ∧
      ∀ C∈D,∀ x∈endpointTriangleVertices C,∀ y∈endpointTriangleVertices C,¬K.Adj x y
  have hA (j:J):1-1/((T j).card:ℝ)^(q+3)≤μ.probability (A j):=by
    have hh:=hNf V (by omega) Q F (S j) (T j) (hST j) hF (hcommon j) (wt j) (hw j) (herr j)
    rw [←finiteLaw_pi_injective_projection_event
      (fun _:E=>FiniteLaw.retentionCoin p hp.le hp1) (f j) (f j).injective] at hh
    apply hh.trans
    apply finiteLaw_probability_mono
    intro σ hσ Y hYU hratio hchange K hK
    have he:(S j∪T j)∩bernoulliVertexSet (fun v=>σ (f j v))=
        (S j∪T j).filter (fun v=>σ (f j v)=true):=by
      ext v;simp [bernoulliVertexSet]
    apply hσ Y hYU hratio _ K hK
    simpa only [he] using hchange
  have hh:=hNc (Fintype.card V) (by omega) (E→Bool) J hJ μ (fun j=>(T j).card) A
    (fun j=>(hcommon j).indices) hA
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ j Y hYU hratio hchange K hK
  obtain ⟨D,hD,havoid⟩:=hσ j Y hYU hratio hchange K hK
  exact ⟨D,hD,endpointFactorGraph_choice (hST j) D Y K hD.1 hD.2 havoid⟩

end Oberwolfach
