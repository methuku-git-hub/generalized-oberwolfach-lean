module

public import Oberwolfach.OrdinaryFreshTriangleInsideRoots
public import Oberwolfach.LocalFactorGraphChoice
public import Oberwolfach.FixedDomainQuadraticEvent
public import Oberwolfach.FiniteProductProjection

@[expose] public section

/-! Simultaneous fresh ordinary factors on the actual fixed domains,
using injective physical sampling coordinates for each root. Coordinates for
different roots may overlap; no independence of their events is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 6500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_fresh_triangle_domains_inside_roots (γ κ b B:ℝ)
    (hγ:0<γ) (hκ:0<κ) (hb:0<b) (hB:0≤B):
    ∃ ε η ζ:ℝ,0<ε ∧ 0<η ∧ 0<ζ ∧
      ∀ (p:ℝ) (hp:0<p) (hp1:p≤1) (q:ℕ),∃ N:ℕ,
      ∀ (V J E:Type) [Fintype V] [DecidableEq V] [Fintype J] [Fintype E] [DecidableEq E],
      N≤Fintype.card V→Fintype.card J≤(Fintype.card V)^2→
      ∀ (Q F:SimpleGraph V) (T:J→Finset V) (f:J→V↪E),
      (∀ j,κ*Fintype.card V≤((T j).card:ℝ))→
      (∀ v,(F.degree v:ℝ)≤ε*Fintype.card V)→
      (∀ j,∀ X:Finset V,X⊆T j→X.card≤3→
        γ*Fintype.card V≤((common (T j) X (fun x=>Q.neighborFinset x)).card:ℝ))→
      ∀ wt:∀ j,LocalOrdinaryCycle Q F (T j) 3→ℝ,
      (∀ j C,b/(Fintype.card V:ℝ)^2≤wt j C ∧ wt j C≤B/(Fintype.card V:ℝ)^2)→
      (∀ j,∀ v∈T j,|1-hypergraphWeightedDegree localOrdinaryVertices (wt j) v|≤η)→
      1-1/(Fintype.card V:ℝ)^q≤
        (FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp.le hp1)).probability
          (fun σ=>∀ j,∀ Y:Finset V,Y⊆T j → 3∣Y.card →
            (((((T j).filter (fun v=>σ (f j v)=true))\Y).card+
              (Y\((T j).filter (fun v=>σ (f j v)=true))).card:ℕ):ℝ)≤ζ*(p*(T j).card)→
            ∀ K:SimpleGraph V,(∀ v,(K.degree v:ℝ)≤ζ*(p*(T j).card))→
            ∃ D:Finset (LocalOrdinaryCycle Q F (T j) 3),
              ((∀ C∈D,∀ E∈D,C≠E→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices E)) ∧
                D.biUnion localOrdinaryVertices=Y) ∧
              localOrdinaryFactorGraph D≤spanningRestriction Q Y ∧
              (∀ v,(localOrdinaryFactorGraph D).degree v≤2) ∧
              Disjoint (localOrdinaryFactorGraph D) K):=by
  obtain ⟨ε,η,ζ,hε,hη,hζ,hbase⟩:=ordinary_fresh_triangle_factor_inside_roots γ κ b B hγ hκ hb hB
  refine ⟨ε,η,ζ,hε,hη,hζ,?_⟩
  intro p hp hp1 q
  obtain ⟨Nf,hNf⟩:=hbase p hp hp1 (q+3)
  obtain ⟨Nc,hNc⟩:=fixed_domain_quadratic_common_event κ hκ q
  refine ⟨max Nf Nc,?_⟩
  intro V J E _ _ _ _ _ hn hJ Q F T f hsize hF hcommon wt hw herr
  let μ:=FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp.le hp1)
  let A:J→(E→Bool)→Prop:=fun j σ=>∀ Y:Finset V,Y⊆T j → 3∣Y.card →
    (((((T j).filter (fun v=>σ (f j v)=true))\Y).card+
      (Y\((T j).filter (fun v=>σ (f j v)=true))).card:ℕ):ℝ)≤ζ*(p*(T j).card)→
    ∀ K:SimpleGraph V,(∀ v,(K.degree v:ℝ)≤ζ*(p*(T j).card))→
    ∃ D:Finset (LocalOrdinaryCycle Q F (T j) 3),
      ((∀ C∈D,∀ E∈D,C≠E→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices E)) ∧
        D.biUnion localOrdinaryVertices=Y) ∧
      ∀ C∈D,∀ x∈localOrdinaryVertices C,∀ y∈localOrdinaryVertices C,¬K.Adj x y
  have hA (j:J):1-1/((T j).card:ℝ)^(q+3)≤μ.probability (A j):=by
    have hh:=hNf V (by omega) Q F (T j) (hsize j) hF (hcommon j) (wt j) (hw j) (herr j)
    rw [←finiteLaw_pi_injective_projection_event
      (fun _:E=>FiniteLaw.retentionCoin p hp.le hp1) (f j) (f j).injective] at hh
    apply hh.trans
    apply finiteLaw_probability_mono
    intro σ hσ Y hYT hdiv hchange K hK
    have he:(T j)∩bernoulliVertexSet (fun v=>σ (f j v))=(T j).filter (fun v=>σ (f j v)=true):=by
      ext v;simp [bernoulliVertexSet]
    apply hσ Y hYT hdiv _ K hK
    simpa only [he] using hchange
  have hh:=hNc (Fintype.card V) (by omega) (E→Bool) J hJ μ (fun j=>(T j).card) A hsize hA
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ j Y hYT hdiv hchange K hK
  exact local_factor_graph_choice Y K (hσ j Y hYT hdiv hchange K hK)

end Oberwolfach
