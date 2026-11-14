module

public import Oberwolfach.OrdinaryLocalEndpointEventLift

@[expose] public section
/-! High-probability endpoint pairings normalized by the size of a fixed
inner physical domain, using the original ambient sampling coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_local_endpoint_probability (p₀ a:ℝ)
    (hp₀:0<p₀) (hp₀1:p₀≤1) (ha:0<a) (ha1:a≤1):
    ∃η ζ:ℝ,0<η ∧ 0<ζ ∧ ∀(b q:ℕ) (p:ℝ) (hp:0<p) (hp1:p≤1),∃N:ℕ,
    ∀(W K E:Type) [Fintype W] [Fintype K] [Fintype E] [DecidableEq W] [DecidableEq K] [DecidableEq E]
      (G F:SimpleGraph W) (T:Finset W) (S R:K→Finset W) (g:K→W↪E) (t:K→ℝ),
    N≤T.card→Fintype.card K≤T.card^2→
    (∀k,S k⊆T)→(∀k,R k⊆T)→(∀k,Disjoint (S k) (R k))→
    (∀k,p₀≤t k ∧ t k≤1)→
    (∀k,a*T.card≤((S k).card:ℝ) ∧ a*T.card≤((R k).card:ℝ))→
    (∀v,F.degree v≤b)→
    (∀k (v:{v:W // v∈T}),v∈ordinaryInducedFinset T (S k)→
      |((((ordinaryInducedFinset T (R k))∩(G.induce (T:Set W)).neighborFinset v).card:ℝ)-
        t k*(ordinaryInducedFinset T (R k)).card)|≤η*(ordinaryInducedFinset T (R k)).card)→
    (∀k (v:{v:W // v∈T}),v∈ordinaryInducedFinset T (R k)→
      |((((ordinaryInducedFinset T (S k))∩(G.induce (T:Set W)).neighborFinset v).card:ℝ)-
        t k*(ordinaryInducedFinset T (S k)).card)|≤η*(ordinaryInducedFinset T (S k)).card)→
    (∀k (v:{v:W // v∈T}),v∈ordinaryInducedFinset T (S k)→∀w,w∈ordinaryInducedFinset T (S k)→
      v≠w→¬(F.induce (T:Set W)).Adj v w→
      ((((ordinaryInducedFinset T (R k))∩(G.induce (T:Set W)).neighborFinset v)∩
        (G.induce (T:Set W)).neighborFinset w).card:ℝ)≤(t k^2+η)*(ordinaryInducedFinset T (R k)).card)→
    1-1/(T.card:ℝ)^q≤(FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp.le hp1)).probability
      (OrdinaryLocalEndpointEvent G F T S R g p ζ):=by
  obtain ⟨η,ζ,hη,hζ,hbase⟩:=fresh_neighbour_pair_physical_event p₀ a hp₀ hp₀1 ha ha1
  refine ⟨η,ζ,hη,hζ,?_⟩
  intro b q p hp hp1
  obtain ⟨N,hN⟩:=hbase b q p hp hp1
  refine ⟨N,?_⟩
  intro W K E _ _ _ _ _ _ G F T S R g t hn hK hST hRT hdis ht hsize hF hrow hcol hcodeg
  let D:Type:={v:W // v∈T}
  let f:K→D↪E:=fun k=>(Function.Embedding.subtype (fun v:W=>v∈T)).trans (g k)
  have hc:Fintype.card D=T.card:=by simp [D]
  have hs:∀k,a*Fintype.card D≤((ordinaryInducedFinset T (S k)).card:ℝ) ∧
      a*Fintype.card D≤((ordinaryInducedFinset T (R k)).card:ℝ):=by
    intro k
    rw [hc,ordinary_induced_finset_card T (S k) (hST k),ordinary_induced_finset_card T (R k) (hRT k)]
    exact hsize k
  have hd:∀k,Disjoint (ordinaryInducedFinset T (S k)) (ordinaryInducedFinset T (R k)):=by
    intro k
    apply Finset.disjoint_left.mpr
    intro v hv hw
    have hv':v.val∈S k:=by simpa [ordinaryInducedFinset] using hv
    have hw':v.val∈R k:=by simpa [ordinaryInducedFinset] using hw
    exact Finset.disjoint_left.mp (hdis k) hv' hw'
  have hdeg:∀(k:K) (v:D),(F.induce (T:Set W)).degree v≤b:=by
    intro k v
    exact (ordinary_induced_degree_le F T v).trans (hF v.val)
  have hprob:=hN D K E (by rw [hc];exact hn) (by rw [hc];exact hK)
    (fun _=>G.induce (T:Set W)) (fun _=>F.induce (T:Set W))
    (fun k=>ordinaryInducedFinset T (S k)) (fun k=>ordinaryInducedFinset T (R k)) t f ht hs hd hdeg hrow hcol hcodeg
  rw [hc] at hprob
  apply hprob.trans
  apply finiteLaw_probability_mono
  intro σ hσ
  apply ordinary_local_endpoint_event_lift G F T S R g p ζ σ hST hRT hdis
  intro k S' R' C hS hR hcs hcr hC hratio
  apply hσ k S' R' C hS hR
  · change ((changed S' ((ordinaryInducedFinset T (S k)).filter (fun v=>σ (g k v.val)=true))).card:ℝ)≤ζ*(p*T.card)
    exact hcs
  · change ((changed R' ((ordinaryInducedFinset T (R k)).filter (fun v=>σ (g k v.val)=true))).card:ℝ)≤ζ*(p*T.card)
    exact hcr
  · intro v
    simpa only [hc] using hC v
  · exact hratio
end Oberwolfach
