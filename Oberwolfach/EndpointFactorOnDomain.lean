module

public import Oberwolfach.EndpointTriangleTransport

@[expose] public section

/-! Apply the exact endpoint-factor theorem on a specified finite domain;
vertices outside that domain impose no ambient-order hypothesis. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem endpoint_triangle_factor_on_domain (γ b B : ℝ) (hγ : 0<γ) (hb : 0<b) (hB : 0≤B) :
    ∃ ε η : ℝ,0<ε ∧ 0<η ∧ ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V],
      ∀ (Q F : SimpleGraph V) (Ω S T : Finset V),N≤Ω.card →
      S⊆Ω → T⊆Ω → Disjoint S T → S.card=2*T.card →
      (∀ v∈Ω,(F.degree v:ℝ)≤ε*Ω.card) →
      EndpointNeighbourCounts Q F S T (γ*Ω.card) →
      ∀ wt : EndpointTriangle Q F S T→ℝ,
      (∀ C,b/(Ω.card:ℝ)^2≤wt C ∧ wt C≤B/(Ω.card:ℝ)^2) →
      (∀ v∈S∪T,|1-hypergraphWeightedDegree endpointTriangleVertices wt v|≤η) →
      HasResourceDecomposition (endpointTriangleVertices (Q:=Q) (F:=F) (S:=S) (T:=T)) (S∪T) := by
  obtain ⟨ε,η,hε,hη,N,hfactor⟩:=endpoint_triangle_factor γ b B hγ hb hB
  refine ⟨ε,η,hε,hη,N,?_⟩
  intro V _ _ Q F Ω S T hn hS hT hST hratio hF hcounts wt hw herr
  let W:=↥Ω
  let e:W↪V:=⟨Subtype.val,Subtype.val_injective⟩
  have hScov:∀ v∈S,∃ w,e w=v:=fun v hv=>⟨⟨v,hS hv⟩,rfl⟩
  have hTcov:∀ v∈T,∃ w,e w=v:=fun v hv=>⟨⟨v,hT hv⟩,rfl⟩
  have hcard:Fintype.card W=Ω.card:=Fintype.card_coe Ω
  have hST':Disjoint (embeddingPullFinset e S) (embeddingPullFinset e T):=by
    apply Finset.disjoint_left.mpr
    intro v hv ht
    exact Finset.disjoint_left.mp hST ((embeddingPullFinset_mem _ _ _).mp hv)
      ((embeddingPullFinset_mem _ _ _).mp ht)
  have hcounts':EndpointNeighbourCounts (Q.comap e) (F.comap e)
      (embeddingPullFinset e S) (embeddingPullFinset e T) (γ*Fintype.card W):=by
    rw [hcard]
    exact endpoint_counts_embedding e Q F S T hScov hTcov _ hcounts
  have hresult:=hfactor W (by simpa only [hcard] using hn) (Q.comap e) (F.comap e)
    (embeddingPullFinset e S) (embeddingPullFinset e T) hST'
    (by simpa only [embeddingPullFinset_card e S hScov,embeddingPullFinset_card e T hTcov] using hratio)
    (by intro v;rw [hcard];exact (Nat.cast_le.mpr (embedding_comap_degree_le e F v)).trans (hF (e v) v.property))
    hcounts' (fun C=>wt (endpointTriangleLift e Q F S T C))
    (by intro C;simpa only [hcard] using hw (endpointTriangleLift e Q F S T C))
    (by
      intro v hv
      rw [endpointTriangleLift_weighted_degree e Q F S T hScov hTcov]
      apply herr
      simpa only [Finset.mem_union,embeddingPullFinset_mem] using hv)
  exact endpointTriangleLift_decomposition e Q F S T hScov hTcov hresult

end Oberwolfach
