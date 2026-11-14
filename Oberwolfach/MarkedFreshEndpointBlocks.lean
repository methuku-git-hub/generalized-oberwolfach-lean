module

public import Oberwolfach.MarkedBoundaryEndpointSampling
public import Oberwolfach.PhysicalBipartiteDomainCounts
public import Oberwolfach.EmbeddedClassChanges

@[expose] public section

/-! All endpoint blocks hold on one physical boundary-sampling event,
including every later permitted change of their actual row and hub classes.
Different blocks and outside roots use the same physical coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_fresh_endpoint_blocks (p₀ a ε:ℝ)
    (hp₀:0<p₀) (hp₀1:p₀≤1) (ha:0<a) (ha1:a≤1) (hε:0<ε) :
    ∃ η ζ:ℝ,0<η ∧ 0<ζ ∧ ∀ (b q:ℕ) (ρ:ℝ) (hρ:0<ρ) (hρ1:ρ≤1),∃ N:ℕ,
    ∀ (V U J:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U] [Fintype J],
      N≤Fintype.card (V⊕U)→Fintype.card J≤(Fintype.card (V⊕U))^2→
    ∀ (π:Equiv.Perm V) (mark incoming:J→Bool) (root:J→V)
      (H:J→V→U→Prop) (F:J→SimpleGraph (V⊕U)) (A:J→Finset V) (B:J→Finset U) (p:J→ℝ),
      (∀ j,p₀≤p j ∧ p j≤1)→
      (∀ j,a*Fintype.card (V⊕U)≤((A j).card:ℝ) ∧ a*Fintype.card (V⊕U)≤((B j).card:ℝ))→
      (∀ j z,(F j).degree z≤b)→
      (∀ j v,v∈A j→|(((B j).filter (H j v)).card:ℝ)-p j*(B j).card|≤η*(B j).card)→
      (∀ j u,u∈B j→|(((A j).filter (fun v=>H j v u)).card:ℝ)-p j*(A j).card|≤η*(A j).card)→
      (∀ j v,v∈A j→∀ w,w∈A j→v≠w→¬(F j).Adj (Sum.inl v) (Sum.inl w)→
        (((B j).filter (fun u=>H j v u∧H j w u)).card:ℝ)≤(p j^2+η)*(B j).card)→
      1-1/(Fintype.card (V⊕U):ℝ)^q≤
      (FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin ρ hρ.le hρ1)).probability
        (fun σ=>∀ j (A':Finset V) (B':Finset U) (D:SimpleGraph (V⊕U)),A'⊆A j→B'⊆B j→
          ((changed A' ((A j).filter (fun v=>σ (markedBoundaryEndpointCoin π (mark j) (incoming j) (root j) (Sum.inl v))=true))).card:ℝ)≤ζ*(ρ*Fintype.card (V⊕U))→
          ((changed B' ((B j).filter (fun u=>σ s(Sum.inl (root j),Sum.inr u)=true))).card:ℝ)≤ζ*(ρ*Fintype.card (V⊕U))→
          (∀ z,(D.degree z:ℝ)≤ζ*(ρ*Fintype.card (V⊕U)))→
          ρ*(A j).card/2≤(A'.card:ℝ) ∧ ρ*(B j).card/2≤(B'.card:ℝ) ∧
          ∀ d tau:ℝ,d≤p₀/2*A'.card→d≤p₀/2*B'.card→ε*A'.card≤tau→ε*B'.card≤tau→
          BipartiteBlockBounds (fun v u=>H j v u∧¬D.Adj (Sum.inl v) (Sum.inr u))
            (fun v=>v∈A') (fun u=>u∈B') d tau (p₀/2)) := by
  obtain ⟨η,ζ,hη,hζ,hfresh⟩:=fresh_bipartite_physical_event p₀ a ε hp₀ hp₀1 ha ha1 hε
  refine ⟨η,ζ,hη,hζ,?_⟩
  intro b q ρ hρ hρ1
  obtain ⟨N,hN⟩:=hfresh b q ρ hρ hρ1
  refine ⟨N,?_⟩
  intro V U J _ _ _ _ _ hn hJ π mark incoming root H F A B p hp hsize hF hrow hcol hcodeg
  let G:=fun j=>ordinaryPhysicalGraph (⊥:SimpleGraph V) (H j)
  let A₁:=fun j=>(A j).image (Sum.inl:V→V⊕U)
  let B₁:=fun j=>(B j).image (Sum.inr:U→V⊕U)
  let f:=fun j=>markedBoundaryEndpointCoin (U:=U) π (mark j) (incoming j) (root j)
  have hrowset (j:J) (v:V):(B₁ j∩(G j).neighborFinset (Sum.inl v))=
      ((B j).filter (H j v)).image Sum.inr:=by
    ext z
    cases z <;> simp [B₁,G,SimpleGraph.mem_neighborFinset,ordinaryPhysicalGraph]
  have hcolset (j:J) (u:U):(A₁ j∩(G j).neighborFinset (Sum.inr u))=
      ((A j).filter (fun v=>H j v u)).image Sum.inl:=by
    ext z
    cases z <;> simp [A₁,G,SimpleGraph.mem_neighborFinset,ordinaryPhysicalGraph]
  have erow (j:J) (v:V):((B₁ j∩(G j).neighborFinset (Sum.inl v)).card)=((B j).filter (H j v)).card:=by
    rw [hrowset,Finset.card_image_of_injective _ Sum.inr_injective]
  have ecol (j:J) (u:U):((A₁ j∩(G j).neighborFinset (Sum.inr u)).card)=((A j).filter (fun v=>H j v u)).card:=by
    rw [hcolset,Finset.card_image_of_injective _ Sum.inl_injective]
  have hh:=hN (V⊕U) J (Sym2 (V⊕U)) hn hJ G F A₁ B₁ p f hp
    (by intro j;simpa only [A₁,B₁,Finset.card_image_of_injective _ Sum.inl_injective,
      Finset.card_image_of_injective _ Sum.inr_injective] using hsize j) hF
    (by
      intro j z hz
      obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hz
      rw [erow]
      simpa only [B₁,Finset.card_image_of_injective _ Sum.inr_injective] using hrow j v hv)
    (by
      intro j z hz
      obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hz
      rw [ecol]
      simpa only [A₁,Finset.card_image_of_injective _ Sum.inl_injective] using hcol j u hu)
    (by
      intro j z hz w hw hne hfw
      obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hz
      obtain ⟨v',hv',rfl⟩:=Finset.mem_image.mp hw
      have ht:=hcodeg j v hv v' hv' (fun he=>hne (congrArg Sum.inl he)) hfw
      simpa only [B₁,G,physical_bipartite_codegree_count,Finset.card_image_of_injective _ Sum.inr_injective] using ht)
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ j A' B' D hAA hBB hca hcb hD
  have hca':((changed (A'.image Sum.inl) ((A₁ j).filter (fun z=>σ (f j z)=true))).card:ℝ)≤ζ*(ρ*Fintype.card (V⊕U)):=by
    have he : (A₁ j).filter (fun z=>σ (f j z)=true)=
        ((A j).filter (fun v=>σ (f j (Sum.inl v))=true)).image Sum.inl := by
      convert filter_image_class (Sum.inl:V→V⊕U) (A j) (fun z=>σ (f j z)=true) using 1 <;> congr!
    rw [he,changed_image_card _ Sum.inl_injective]
    exact hca
  have hcb':((changed (B'.image Sum.inr) ((B₁ j).filter (fun z=>σ (f j z)=true))).card:ℝ)≤ζ*(ρ*Fintype.card (V⊕U)):=by
    have he : (B₁ j).filter (fun z=>σ (f j z)=true)=
        ((B j).filter (fun u=>σ (f j (Sum.inr u))=true)).image Sum.inr := by
      convert filter_image_class (Sum.inr:U→V⊕U) (B j) (fun z=>σ (f j z)=true) using 1 <;> congr!
    rw [he,changed_image_card _ Sum.inr_injective]
    simpa only [f,marked_boundary_endpoint_spoke_coin] using hcb
  obtain ⟨hsa,hsb,hr,hc,hcut⟩:=hσ j (A'.image Sum.inl) (B'.image Sum.inr) D
    (Finset.image_subset_image hAA) (Finset.image_subset_image hBB) hca' hcb' hD
  simp only [A₁,B₁,Finset.card_image_of_injective _ Sum.inl_injective,
    Finset.card_image_of_injective _ Sum.inr_injective] at hsa hsb hr hc hcut
  refine ⟨hsa,hsb,?_⟩
  intro d tau hdA hdB htA htB
  apply physical_bipartite_block_from_counts (H j) D A' B' d tau (p₀/2)
  · intro v hv
    exact hdB.trans (hr _ (Finset.mem_image.mpr ⟨v,hv,rfl⟩))
  · intro u hu
    exact hdA.trans (hc _ (Finset.mem_image.mpr ⟨u,hu,rfl⟩))
  · intro S hS T hT hs ht
    exact hcut S hS T hT (htA.trans hs) (htB.trans ht)

end Oberwolfach
