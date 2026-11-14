module

public import Oberwolfach.MarkedMixedBoundarySelection
public import Oberwolfach.MarkedEndpointAssignmentIncidences
public import Oberwolfach.FiniteFibreCounts

@[expose] public section

/-! The actual mixed physical degree bound supplies both construction
budgets and the number of boundary paths. The paths may share a hub;
their occurrences are counted using disjoint selected spoke graphs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E T J I:Type} [Fintype V] [Fintype U] [Fintype J] [Fintype I]
  [DecidableEq V] [DecidableEq U] [DecidableEq J] [DecidableEq I]
  {tail head:E→V} {ktail khead:T→V} {m b:ℕ} {π:Equiv.Perm V} {H₀ HK:V→U→Prop}

theorem marked_endpoint_assignment_total
    (A₀ A₁ X₀ X₁:I→Finset V) (Y₀ Y₁:I→Finset U)
    (Q:∀ i,MarkedEndpointPairing (A₀ i) (A₁ i) (X₀ i) (X₁ i) (Y₀ i) (Y₁ i) H₀ HK π b)
    (hcross:∀ i j,i≠j→Disjoint (Q i).graph (Q j).graph)
    (D:ℕ) (hD:∀ w,(⨆ i,(Q i).graph).degree w≤D):
    Fintype.card (Σ i,Y₀ i⊕Y₁ i)≤Fintype.card U*D := by
  apply finite_fibre_card_bound (MarkedEndpointPairing.assignedHub Q) D
  intro u
  have hh:=(MarkedEndpointPairing.assigned_hub_occurrences Q hcross u).trans (hD (Sum.inr u))
  simpa only [Fintype.card_subtype] using hh

theorem marked_mixed_selection_bounds (hub:J→U) (Y:J→Finset V)
    (P:∀ j,MarkedHubFactorOn tail head ktail khead m π b H₀ HK (hub j) (Y j))
    (A₀ A₁ X₀ X₁:I→Finset V) (Y₀ Y₁:I→Finset U)
    (Q:∀ i,MarkedEndpointPairing (A₀ i) (A₁ i) (X₀ i) (X₁ i) (Y₀ i) (Y₁ i) H₀ HK π b)
    (D:ℕ)
    (hcross:∀ i j:J⊕I,i≠j→Disjoint
      (Sum.elim (fun j=>(P j).graph) (fun i=>(Q i).graph) i)
      (Sum.elim (fun j=>(P j).graph) (fun i=>(Q i).graph) j))
    (hD:∀ w,(⨆ i:J⊕I,Sum.elim (fun j=>(P j).graph) (fun i=>(Q i).graph) i).degree w≤D):
    (∀ j k,j≠k→Disjoint (P j).rim (P k).rim)∧
    (∀ i j,i≠j→Disjoint (Q i).graph (Q j).graph)∧
    (∀ v,(⨆ j,(P j).rim).degree v≤D)∧
    (∀ w,(⨆ i,(Q i).graph).degree w≤D)∧
    Fintype.card (Σ i,Y₀ i⊕Y₁ i)≤Fintype.card U*D := by
  let G:SimpleGraph (V⊕U):=⨆ i:J⊕I,Sum.elim (fun j=>(P j).graph) (fun i=>(Q i).graph) i
  have hQcross:∀ i j,i≠j→Disjoint (Q i).graph (Q j).graph:=by
    intro i j hij
    exact hcross (Sum.inr i) (Sum.inr j) (fun he=>hij (Sum.inr.inj he))
  have hQle:(⨆ i,(Q i).graph)≤G:=by
    apply iSup_le
    intro i
    exact le_iSup_of_le (Sum.inr i) le_rfl
  have hQdegree (w:V⊕U):(⨆ i,(Q i).graph).degree w≤D:=
    (SimpleGraph.degree_le_of_le hQle).trans (hD w)
  have hPle:(⨆ j,(P j).rim)≤G.comap (Sum.inl:V→V⊕U):=by
    intro v z hvz
    obtain ⟨j,hj⟩:=SimpleGraph.iSup_adj.mp hvz
    change G.Adj (Sum.inl v) (Sum.inl z)
    apply SimpleGraph.iSup_adj.mpr
    refine ⟨Sum.inl j,?_⟩
    change ((P j).rim.map (Sum.inl:V→V⊕U)).Adj _ _
    rw [SimpleGraph.map_adj']
    exact ⟨fun he=>(P j).rim.ne_of_adj hj (Sum.inl.inj he),v,z,hj,rfl,rfl⟩
  refine ⟨?_,hQcross,?_,hQdegree,marked_endpoint_assignment_total A₀ A₁ X₀ X₁ Y₀ Y₁ Q hQcross D hQdegree⟩
  · intro j k hjk
    apply disjoint_iff_inf_le.mpr
    intro v z hvz
    have hdis:=hcross (Sum.inl j) (Sum.inl k) (fun he=>hjk (Sum.inl.inj he))
    apply (disjoint_graphs_no_common_edge _ _ hdis (Sum.inl v) (Sum.inl z) _ _).elim
    · change ((P j).rim.map (Sum.inl:V→V⊕U)).Adj _ _
      rw [SimpleGraph.map_adj']
      exact ⟨fun he=>(P j).rim.ne_of_adj hvz.1 (Sum.inl.inj he),v,z,hvz.1,rfl,rfl⟩
    · change ((P k).rim.map (Sum.inl:V→V⊕U)).Adj _ _
      rw [SimpleGraph.map_adj']
      exact ⟨fun he=>(P k).rim.ne_of_adj hvz.2 (Sum.inl.inj he),v,z,hvz.2,rfl,rfl⟩
  · intro v
    exact (SimpleGraph.degree_le_of_le hPle).trans
      ((graph_comap_degree_le G ⟨Sum.inl,Sum.inl_injective⟩ v).trans (hD (Sum.inl v)))

end Oberwolfach
