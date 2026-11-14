module

public import Oberwolfach.EndpointDeepCountsPhysical
public import Oberwolfach.OrdinaryEndpointPhysicalGeometry
public import Oberwolfach.OrdinaryEndpointEligibleGeometry

@[expose] public section
/-! The endpoint common-neighborhood input follows from the deeper physical
row and hub counts, with the original degree and size margins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
set_option synthInstance.maxSize 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem endpoint_neighborhoods_from_deep_counts
    (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U)
    (γ κ p pR pH ε L:ℝ) (hp:0<p) (hp1:p≤1) (hpR:p≤pR) (hpH:p≤pH) (hκ:0<κ)
    (hB:κ*A.card≤(B.card:ℝ)) (hL:0≤L) (hLA:L≤(A.card:ℝ)/24)
    (hε:ε≤min (p^4/16) (p^3/2))
    (hscale:γ*Fintype.card (V⊕U)≤endpointCountCoefficient p κ*A.card)
    (hdeg:∀x∉A,∀v∈insert x A,(3/4:ℝ)*A.card≤((A∩P.neighborFinset v).card:ℝ))
    (hF:∀v:V⊕U,((ordinaryPhysicalGraph F (fun _ _=>False)).degree v:ℝ)≤L)
    (hQ:(ordinaryPhysicalGraph (U:=U) Q (fun _ _=>False))≤
      (ordinaryPhysicalGraph P (fun _ _=>False))\(ordinaryPhysicalGraph F (fun _ _=>False)))
    (data:EndpointPhysicalDeepCounts P Q F H A B pR pH ε):
    ∀i:{v:V // v∉A},EndpointNeighbourCounts
      (ordinaryPhysicalGraph (spanningRestriction Q A) (fun v u=>H v u∧v∈A∧u∈B))
      (ordinaryPhysicalGraph F (fun _ _=>False))
      ((ordinaryBoundaryRimSet Q A i).image Sum.inl) ((ordinaryBoundaryRowSet H A B i).image Sum.inr)
      (γ*Fintype.card (V⊕U)):=by
  intro i
  have hA:(A.image (Sum.inl:V→V⊕U)).card=A.card:=Finset.card_image_of_injective _ Sum.inl_injective
  have hBc:(B.image (Sum.inr:U→V⊕U)).card=B.card:=Finset.card_image_of_injective _ Sum.inr_injective
  have hdis:Disjoint (A.image (Sum.inl:V→V⊕U)) (B.image Sum.inr):=by
    apply Finset.disjoint_left.mpr
    intro z hzA hzB
    cases z with
    | inl v=>simp at hzB
    | inr u=>simp at hzA
  have hdegree:∀v∈insert (Sum.inl i.val) (A.image (Sum.inl:V→V⊕U)),
      (3/4:ℝ)*(A.image (Sum.inl:V→V⊕U)).card≤
        (((A.image (Sum.inl:V→V⊕U))∩(ordinaryPhysicalGraph P (fun _ _=>False)).neighborFinset v).card:ℝ):=by
    intro v hv
    have hv':v∈(insert i.val A).image (Sum.inl:V→V⊕U):=by simpa only [Finset.image_insert] using hv
    obtain ⟨v₀,hv₀,rfl⟩:=Finset.mem_image.mp hv'
    rw [ordinary_endpoint_parent_neighbors]
    simp only [Finset.card_image_of_injective _ Sum.inl_injective]
    exact hdeg i.val i.property v₀ hv₀
  have hleft (S:Finset (V⊕U)) (hS:S⊆insert (Sum.inl i.val) (A.image Sum.inl)):
      S⊆Finset.univ.image (Sum.inl:V→V⊕U):=by
    intro z hz
    rcases Finset.mem_insert.mp (hS hz) with rfl|hzA
    · exact Finset.mem_image.mpr ⟨i.val,Finset.mem_univ _,rfl⟩
    · obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hzA
      exact Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩
  have hrows:∀S J:Finset (V⊕U),Sum.inl i.val∈S→S⊆insert (Sum.inl i.val) (A.image Sum.inl)→
      J⊆B.image Sum.inr→S.card≤3→J.card≤2→S.card+J.card≤4→
      pR^S.card*pH^J.card*(common (A.image Sum.inl) S
        (fun v=>((ordinaryPhysicalGraph P (fun _ _=>False))\(ordinaryPhysicalGraph F (fun _ _=>False))).neighborFinset v)).card-
        ε*(A.image (Sum.inl:V→V⊕U)).card≤((common (common (A.image Sum.inl) S
          (fun v=>(ordinaryPhysicalGraph Q (fun _ _=>False)).neighborFinset v)) J
          (fun u=>(ordinaryPhysicalGraph ⊥ H).neighborFinset u)).card:ℝ):=by
    intro S J hx hS hJ hSc hJc hSJ
    simpa only [hA] using data.rows S J (hleft S hS) hJ hSc hJc hSJ
  have hind:∀S:Finset (V⊕U),Sum.inl i.val∈S→S⊆insert (Sum.inl i.val) (A.image Sum.inl)→
      (S.card=1∨S.card=3)→(∀v∈S,∀w∈S,¬(ordinaryPhysicalGraph F (fun _ _=>False)).Adj v w)→
      (pH^S.card-ε)*(B.image (Sum.inr:U→V⊕U)).card≤
        ((common (B.image Sum.inr) S (fun v=>(ordinaryPhysicalGraph ⊥ H).neighborFinset v)).card:ℝ):=by
    intro S hx hS hc hfree
    simpa only [hBc] using data.indices S (hleft S hS) (by omega) hfree
  have hc:=endpoint_source_counts (ordinaryPhysicalGraph P (fun _ _=>False))
    (ordinaryPhysicalGraph Q (fun _ _=>False)) (ordinaryPhysicalGraph ⊥ H)
    (ordinaryPhysicalGraph F (fun _ _=>False)) (A.image Sum.inl) (B.image Sum.inr) (Sum.inl i.val)
    hdis hQ p pR pH ε L κ hp hp1 hpR hpH hκ (by simpa only [hA,hBc] using hB) hL
    (by simpa only [hA] using hLA) hε hdegree hF hrows hind
  rw [ordinary_endpoint_host_physical_geometry,ordinary_endpoint_row_domain Q A i,
    ordinary_endpoint_index_domain H A B i] at hc
  have hscale':γ*Fintype.card (V⊕U)≤endpointCountCoefficient p κ*(A.image (Sum.inl:V→V⊕U)).card:=by
    simpa only [hA] using hscale
  exact ⟨hscale'.trans hc.indices,fun Y J hY hJ hYc hJc hYJ=>hscale'.trans (hc.rows Y J hY hJ hYc hJc hYJ),
    fun v hv w hw hvw hfree=>hscale'.trans (hc.pairs v hv w hw hvw hfree)⟩
end Oberwolfach
