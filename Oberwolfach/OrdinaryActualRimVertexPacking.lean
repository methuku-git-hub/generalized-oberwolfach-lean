module

public import Oberwolfach.OrdinaryActualRimWheels
public import Oberwolfach.OrdinaryActualVertexWheels
public import Oberwolfach.TransformerUnusedEndpointSpokes
public import Oberwolfach.TransformerCrossAttachmentDisjointness

@[expose] public section

/-! Both cross-family intersections in the ordinary transformer: first
rim-edge wheels against second vertex wheels, and conversely. The reused
endpoints and shifted hubs are the actual incidence-based assignments. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

 theorem ordinary_actual_rim_vertex_packing (G Q F:SimpleGraph V) (H₀ H:V→U→Prop) (φ:V→V)
    (b:∀ v,G.neighborSet v≃({u:U // H₀ v u}×Fin 2))
    (σ:∀ v,Equiv.Perm (G.neighborSet v)) (hσ:∀ v w,σ v w≠w)
    (p:(G.edgeFinset⊕{e:V×U // H₀ e.1 e.2})→(Σ a:V,Σ c:V,Q.Walk a c))
    (r:ℕ) (hr:3≤r) (R W:Finset V) (B:Finset U) (hRW:R⊆W)
    (hroot:∀ v∈G.support,v∈R∧φ v∈R)
    (hcross:∀ v∈G.support,∀ w∈G.support,φ v≠w)
    (hpW:∀ i,∀ v∈(p i).2.2.support,v∈W∧v∉R)
    (hdis:∀ i j,i≠j→Disjoint (p i).2.2.support.toFinset (p j).2.2.support.toFinset)
    (E:OrdinaryActualRimWheels G Q F H₀ H φ r B b σ p)
    (D:∀ d:Σ v,G.neighborSet v,
      OrdinaryVertexWheelPair Q F H r d.1 (φ d.1)
        (transformerRimEndpoint G Q H₀ p d) (transformerSpokeEndpoint G Q H₀ b p d)
        (transformerAssignedHub G σ E.hub d))
    (hD:∀ d,∀ v∈rootWheelInternal (D d).first d.1 (transformerRimEndpoint G Q H₀ p d)
        (transformerSpokeEndpoint G Q H₀ b p d),v∉W∧v≠φ d.1):
    ∀ e d,
      Disjoint (ordinaryWheelResources (E.first e)) (ordinaryWheelResources (D d).second) ∧
      Disjoint (ordinaryWheelResources (E.second e)) (ordinaryWheelResources (D d).first):=by
  have hs (e:G.edgeFinset) (v:V) (hv:v∈(ordinaryWheelRim (E.first e)).support):
      v∈R∨v∈(p (.inl e)).2.2.support:=by
    have he:=edge_out_adj G e
    rcases (E.first_support e v).mp hv with rfl|rfl|hv
    · exact Or.inl (hroot _ he.mem_support_left).1
    · exact Or.inl (hroot _ he.mem_support_right).1
    · exact Or.inr hv
  have hs' (e:G.edgeFinset) (v:V) (hv:v∈(ordinaryWheelRim (E.second e)).support):
      v∈R∨v∈(p (.inl e)).2.2.support:=by
    have he:=edge_out_adj G e
    rcases (E.second_support e v).mp hv with rfl|rfl|hv
    · exact Or.inl (hroot _ he.mem_support_left).2
    · exact Or.inl (hroot _ he.mem_support_right).2
    · exact Or.inr hv
  have hSW (e:G.edgeFinset) (v:V) (hv:v∈(ordinaryWheelRim (E.first e)).support):v∈W:=by
    rcases hs e v hv with hv|hv
    · exact hRW hv
    · exact (hpW _ _ hv).1
  have hS'W (e:G.edgeFinset) (v:V) (hv:v∈(ordinaryWheelRim (E.second e)).support):v∈W:=by
    rcases hs' e v hv with hv|hv
    · exact hRW hv
    · exact (hpW _ _ hv).1
  have hu:=actual_attachment_spokes_unused G Q F H₀ H b σ hσ E.hub p R
    (fun i v hv=>(hpW i v hv).2) hdis r E.first E.first_hub hs
  have hu':=actual_attachment_spokes_unused G Q F H₀ H b σ hσ E.hub p R
    (fun i v hv=>(hpW i v hv).2) hdis r E.second E.second_hub hs'
  intro e d
  have hd:G.Adj d.1 d.2.val:=d.2.property
  have hde:=hd.mem_support_left
  have he:=edge_out_adj G e
  have hnot:φ d.1∉(ordinaryWheelRim (E.first e)).support:=by
    intro hm
    rcases (E.first_support e _).mp hm with hh|hh|hh
    · exact hcross _ hde _ he.mem_support_left hh
    · exact hcross _ hde _ he.mem_support_right hh
    · exact (hpW _ _ hh).2 (hroot _ hde).2
  have hnot':d.1∉(ordinaryWheelRim (E.second e)).support:=by
    intro hm
    rcases (E.second_support e _).mp hm with hh|hh|hh
    · exact hcross _ he.mem_support_left _ hde hh.symm
    · exact hcross _ he.mem_support_right _ hde hh.symm
    · exact (hpW _ _ hh).2 (hroot _ hde).1
  have hznot (C:G.edgeFinset→OrdinaryWheel Q F H r)
      (hsC:∀ e,∀ v∈(ordinaryWheelRim (C e)).support,v∈R∨v∈(p (.inl e)).2.2.support):
      transformerSpokeEndpoint G Q H₀ b p d∉(ordinaryWheelRim (C e)).support:=by
    intro hv
    have hz:=graphPathEndpoint_mem (p (.inr (spokeEndpointEquiv G H₀ b d).1)) (spokeEndpointEquiv G H₀ b d).2
    change transformerSpokeEndpoint G Q H₀ b p d∈_ at hz
    rcases hsC e _ hv with hR|hp
    · exact (hpW _ _ hz).2 hR
    · exact Finset.disjoint_left.mp (hdis (.inl e) (.inr (spokeEndpointEquiv G H₀ b d).1) Sum.inl_ne_inr)
        (List.mem_toFinset.mpr hp) (List.mem_toFinset.mpr hz)
  have hInt:=vertex_pair_internal_second (D d) (fun v hv=>(hD d v hv).2)
  constructor
  · apply edge_vertex_wheels_disjoint_without_attachment (E.first e) (D d).second (φ d.1)
      (transformerRimEndpoint G Q H₀ p d) (transformerSpokeEndpoint G Q H₀ b p d)
      (D d).second_a (D d).second_b (fun hadj=>hznot E.first hs hadj.mem_support_right) hnot
    · intro v hv hw
      rw [hInt] at hv
      exact (hD d v hv).1 (hSW e v hw)
    · rw [(D d).second_hub];exact (hu e d).1
    · rw [(D d).second_hub];exact (hu e d).2
  · apply edge_vertex_wheels_disjoint_without_attachment (E.second e) (D d).first d.1
      (transformerRimEndpoint G Q H₀ p d) (transformerSpokeEndpoint G Q H₀ b p d)
      (D d).first_a (D d).first_b (fun hadj=>hznot E.second hs' hadj.mem_support_right) hnot'
    · intro v hv hw
      exact (hD d v hv).1 (hS'W e v hw)
    · rw [(D d).first_hub];exact (hu' e d).1
    · rw [(D d).first_hub];exact (hu' e d).2

end Oberwolfach
