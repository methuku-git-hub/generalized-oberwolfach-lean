module

public import Oberwolfach.MarkedResourceDegreeUpper
public import Oberwolfach.PhysicalHostDegreeBounds
public import Oberwolfach.MarkedInnerResources
public import Oberwolfach.MarkedPhysicalAuxiliaryIncidence

@[expose] public section

/-! The active packing's three physical degree bounds control all physical
and auxiliary incidences inside the specified pair of vertex sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V} {H₀ HK:V→U→Prop}

theorem marked_packing_inner_physical_incidence_bound
    (hm:1≤m) (hb:1≤b) (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (X:Finset V) (Z:Finset U) (C:ℝ) (hC:0≤C)
    (hr:∀ v,((spanningRestriction (markedPackingRimGraph M) X).degree v:ℝ)≤C)
    (hv:∀ v∈X,((Z.filter (markedPackingSpokes M v)).card:ℝ)≤C)
    (hu:∀ u∈Z,((X.filter (fun v=>markedPackingSpokes M v u)).card:ℝ)≤C)
    (x:V⊕U):
    ((((M.biUnion markedWheelPhysicalResources).filter (markedInnerResource X Z)).filter
      (markedPhysicalIncident x)).card:ℝ)≤2*C:=by
  let S:=(M.biUnion markedWheelPhysicalResources).filter (markedInnerResource X Z)
  let Q:=spanningRestriction (markedPackingRimGraph M) X
  let H:=fun v u=>v∈X∧u∈Z∧markedPackingSpokes M v u
  have hpairs:∀ e,Sum.inl e∈S→e.card=2:=by
    intro e he
    obtain ⟨W,hW,hWe⟩:=Finset.mem_biUnion.mp (Finset.mem_filter.mp he).1
    obtain ⟨i,hi,heq⟩:=Finset.mem_image.mp ((markedWheelPhysicalResources_rim W e).mp hWe)
    have hc:=markedCycle_physical_edge_card tail head ktail khead m π b hm hb W.1 i
    simpa only [←heq,Function.comp_apply] using hc
  have hrow:∀ v,((Finset.univ.filter (H v)).card:ℝ)≤C:=by
    intro v
    by_cases hx:v∈X
    · have he:Finset.univ.filter (H v)=Z.filter (markedPackingSpokes M v):=by
        ext u;simp only [H,hx,true_and,Finset.mem_filter,Finset.mem_univ]
      rw [he];exact hv v hx
    · have he:Finset.univ.filter (H v)=∅:=by
        ext u;simp only [H,hx,false_and,Finset.mem_filter,Finset.notMem_empty,iff_false,and_false]
      rw [he,Finset.card_empty,Nat.cast_zero];exact hC
  have hcol:∀ u,((Finset.univ.filter (fun v=>H v u)).card:ℝ)≤C:=by
    intro u
    by_cases hz:u∈Z
    · have he:Finset.univ.filter (fun v=>H v u)=X.filter (fun v=>markedPackingSpokes M v u):=by
        ext v;simp only [H,hz,true_and,Finset.mem_filter,Finset.mem_univ]
      rw [he];exact hu u hz
    · have he:Finset.univ.filter (fun v=>H v u)=∅:=by
        ext v;simp only [H,hz,false_and,Finset.mem_filter,Finset.notMem_empty,iff_false,and_false]
      rw [he,Finset.card_empty,Nat.cast_zero];exact hC
  have hbound:=ordinary_physical_degree_bound Q H C C C (2*C) hr
    (fun v=>by simpa only [←Set.ncard_coe_finset,Finset.coe_filter] using hrow v)
    (fun u=>by simpa only [←Set.ncard_coe_finset,Finset.coe_filter] using hcol u)
    (by linarith) (by linarith)
  have hc:=marked_incident_card_le_graph_degree (ordinaryPhysicalGraph Q H) S hpairs (by
    intro v w he
    have hpair:=hpairs {v,w} he
    have hne:v≠w:=by intro h;subst w;simp at hpair
    obtain ⟨hmem,hinner⟩:=Finset.mem_filter.mp he
    exact (spanningRestriction_adj _ X v w).mpr ⟨⟨hne,(markedPackingResources_rim M {v,w}).mp hmem⟩,
      hinner (by simp),hinner (by simp)⟩) (by
    intro v u he
    obtain ⟨hmem,hinner⟩:=Finset.mem_filter.mp he
    exact ⟨hinner.1,hinner.2,(markedPackingResources_spoke M v u).mp hmem⟩) x
  exact (Nat.cast_le.mpr hc).trans (hbound x)

theorem marked_packing_inner_both_incidence_bound [Fintype E] [Fintype K]
    (hm:1≤m) (hb:1≤b)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (X:Finset V) (Z:Finset U) (C:ℝ) (hC:0≤C)
    (hr:∀ v,((spanningRestriction (markedPackingRimGraph M) X).degree v:ℝ)≤C)
    (hv:∀ v∈X,((Z.filter (markedPackingSpokes M v)).card:ℝ)≤C)
    (hu:∀ u∈Z,((X.filter (fun v=>markedPackingSpokes M v u)).card:ℝ)≤C)
    (physical:Bool) (x:V⊕U):
    (((markedIncidentEdges tail head ktail khead π H₀ HK physical x).filter
      (fun e=>markedActivePhysical tail head ktail khead π H₀ HK e∈
        (M.biUnion markedWheelPhysicalResources).filter (markedInnerResource X Z))).card:ℝ)≤4*C:=by
  have hh:=marked_incidence_bound_from_physical_resources tail head ktail khead π H₀ HK hp
    ((M.biUnion markedWheelPhysicalResources).filter (markedInnerResource X Z)) (2*C)
    (marked_packing_inner_physical_incidence_bound hm hb M X Z C hC hr hv hu) physical x
  linarith only [hh]

end Oberwolfach
