module

public import Oberwolfach.OrdinaryFreshFactorNormalizedDomain
public import Oberwolfach.FixedDomainQuadraticEvent

@[expose] public section
/-! Fresh factors simultaneously on a family of actual domains. The
coordinates for different domains may overlap: a union bound, not an
independence assumption, combines their events. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_fresh_normalized_domain_family
    (m:ℕ) (hm:2≤m) (γ κ b B:ℝ) (hγ:0<γ) (hκ:0<κ) (hb:0<b) (hB:0≤B):
    ∃ε η ζ:ℝ,0<ε ∧ 0<η ∧ 0<ζ ∧ ∀(p:ℝ) (hp:0<p) (hp1:p≤1) (q:ℕ),∃N:ℕ,
    ∀(n:ℕ),N≤n→∀(J E:Type) [Fintype J] [Fintype E] [DecidableEq E]
      (A:J→Type) [∀j,Fintype (A j)] [∀j,DecidableEq (A j)],
    Fintype.card J≤n^2→(∀j,κ*n≤(Fintype.card (A j):ℝ))→
    ∀(f:∀j,A j↪E) (Q F:∀j,SimpleGraph (A j)),
    (∀j v,((F j).degree v:ℝ)≤ε*Fintype.card (A j))→
    (∀j,∀S:Finset (A j),S.card≤(if m=2 then 3 else 2)→
      γ*Fintype.card (A j)≤((common Finset.univ S (fun x=>(Q j).neighborFinset x)).card:ℝ))→
    ∀wt:∀j,LocalOrdinaryCycle (Q j) (F j) Finset.univ (m+1)→ℝ,
    (∀j C,b/(Fintype.card (A j):ℝ)^m≤wt j C ∧ wt j C≤B/(Fintype.card (A j):ℝ)^m)→
    (∀j v,|1-hypergraphWeightedDegree localOrdinaryVertices (wt j) v|≤η)→
    1-1/(n:ℝ)^q≤(FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp.le hp1)).probability
      (fun σ=>∀j,∀Y:Finset (A j),(m+1)∣Y.card→
        ((((Finset.univ∩bernoulliVertexSet (fun a=>σ (f j a)))\Y).card+
          (Y\(Finset.univ∩bernoulliVertexSet (fun a=>σ (f j a)))).card:ℕ):ℝ)≤ζ*(p*Fintype.card (A j))→
        ∀K:SimpleGraph (A j),(∀v,(K.degree v:ℝ)≤ζ*(p*Fintype.card (A j)))→
        ∃D:Finset (LocalOrdinaryCycle (Q j) (F j) Finset.univ (m+1)),
          ((∀C∈D,∀C'∈D,C≠C'→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices C')) ∧
            D.biUnion localOrdinaryVertices=Y) ∧
          ∀C∈D,∀x∈localOrdinaryVertices C,∀y∈localOrdinaryVertices C,¬K.Adj x y):=by
  obtain ⟨ε,η,ζ,hε,hη,hζ,hbase⟩:=ordinary_fresh_factor_normalized_domain_probability m hm γ b B hγ hb hB
  refine ⟨ε,η,ζ,hε,hη,hζ,?_⟩
  intro p hp hp1 q
  obtain ⟨Nf,hNf⟩:=hbase p hp hp1 (q+3)
  obtain ⟨Nc,hNc⟩:=fixed_domain_quadratic_common_event κ hκ q
  obtain ⟨M,hM⟩:=exists_nat_gt ((Nf:ℝ)/κ)
  refine ⟨max Nc M,?_⟩
  intro n hn J E _ _ _ A _ _ hJ hsize f Q F hF hcommon wt hw hload
  let μ:=FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp.le hp1)
  let Good:=fun j (σ:E→Bool)=>∀Y:Finset (A j),(m+1)∣Y.card→
    ((((Finset.univ∩bernoulliVertexSet (fun a=>σ (f j a)))\Y).card+
      (Y\(Finset.univ∩bernoulliVertexSet (fun a=>σ (f j a)))).card:ℕ):ℝ)≤ζ*(p*Fintype.card (A j))→
    ∀K:SimpleGraph (A j),(∀v,(K.degree v:ℝ)≤ζ*(p*Fintype.card (A j)))→
    ∃D:Finset (LocalOrdinaryCycle (Q j) (F j) Finset.univ (m+1)),
      ((∀C∈D,∀C'∈D,C≠C'→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices C')) ∧
        D.biUnion localOrdinaryVertices=Y) ∧
      ∀C∈D,∀x∈localOrdinaryVertices C,∀y∈localOrdinaryVertices C,¬K.Adj x y
  have hlocal (j:J):1-1/(Fintype.card (A j):ℝ)^(q+3)≤μ.probability (Good j):=by
    have hnM:(M:ℝ)≤n:=by exact_mod_cast (show M≤n by omega)
    have hNfactor:(Nf:ℝ)≤Fintype.card (A j):=by
      have hh:((Nf:ℝ)/κ)*κ≤(n:ℝ)*κ:=mul_le_mul_of_nonneg_right (hM.le.trans hnM) hκ.le
      have he:((Nf:ℝ)/κ)*κ=Nf:=div_mul_cancel₀ _ hκ.ne'
      rw [he] at hh
      nlinarith only [hh,hsize j]
    have hNfn:Nf≤Fintype.card (A j):=by exact_mod_cast hNfactor
    exact hNf (A j) E hNfn (f j) (Q j) (F j) (hF j) (hcommon j) (wt j) (hw j) (hload j)
  exact hNc n (by omega) (E→Bool) J hJ μ (fun j=>Fintype.card (A j)) Good hsize hlocal
end Oberwolfach
