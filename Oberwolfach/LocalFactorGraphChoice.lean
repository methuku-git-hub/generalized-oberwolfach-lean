module

public import Oberwolfach.OrdinaryFactorWheels
public import Oberwolfach.InducedFractionalCycles

@[expose] public section

/-! The actual simple graph formed by a local cycle factor. The selected
cycle identifiers remain available, with exact support, degree and avoidance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V] {Q F:SimpleGraph V} {T:Finset V} {r:ℕ}

def localOrdinaryFactorGraph (M:Finset (LocalOrdinaryCycle Q F T r)):SimpleGraph V:=
  ordinaryFactorGraph (M.image Subtype.val)

theorem localOrdinaryFactorGraph_adj (M:Finset (LocalOrdinaryCycle Q F T r)) (x y:V):
    (localOrdinaryFactorGraph M).Adj x y↔∃ C∈M,C.val.val.val.Adj x y:=by
  simp only [localOrdinaryFactorGraph,ordinaryFactorGraph,SimpleGraph.iSup_adj,Finset.mem_image]
  constructor
  · rintro ⟨_,⟨C,hC,rfl⟩,hxy⟩;exact ⟨C,hC,hxy⟩
  · rintro ⟨C,hC,hxy⟩;exact ⟨C.val,⟨C,hC,rfl⟩,hxy⟩

theorem localOrdinaryFactorGraph_support (M:Finset (LocalOrdinaryCycle Q F T r)):
    (localOrdinaryFactorGraph M).support.toFinset=M.biUnion localOrdinaryVertices:=by
  ext v
  simp only [Set.mem_toFinset,SimpleGraph.mem_support,localOrdinaryFactorGraph_adj,
    Finset.mem_biUnion,localOrdinaryVertices,Set.mem_toFinset,SimpleGraph.mem_support]
  constructor
  · rintro ⟨w,C,hC,h⟩;exact ⟨C,hC,w,h⟩
  · rintro ⟨C,hC,w,h⟩;exact ⟨w,C,hC,h⟩

theorem localOrdinaryFactorGraph_degree (M:Finset (LocalOrdinaryCycle Q F T r))
    (hM:∀ C∈M,∀ D∈M,C≠D→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices D))
    (v:V):(localOrdinaryFactorGraph M).degree v≤2:=by
  apply ordinaryFactorGraph_degree_le_two
  intro C hC D hD hne
  obtain ⟨C',hC',rfl⟩:=Finset.mem_image.mp hC
  obtain ⟨D',hD',rfl⟩:=Finset.mem_image.mp hD
  exact hM C' hC' D' hD' (fun h=>hne (congrArg Subtype.val h))

theorem localOrdinaryFactorGraph_restriction (M:Finset (LocalOrdinaryCycle Q F T r))
    (Y:Finset V) (hY:M.biUnion localOrdinaryVertices=Y):
    localOrdinaryFactorGraph M≤spanningRestriction Q Y:=by
  intro x y hxy
  obtain ⟨C,hC,hxy⟩:=(localOrdinaryFactorGraph_adj M x y).mp hxy
  apply (spanningRestriction_adj Q Y x y).mpr
  have hsub:localOrdinaryVertices C⊆Y:=by rw [←hY];exact Finset.subset_biUnion_of_mem _ hC
  exact ⟨C.val.property hxy,hsub (Set.mem_toFinset.mpr hxy.mem_support_left),
    hsub (Set.mem_toFinset.mpr hxy.mem_support_right)⟩

theorem localOrdinaryFactorGraph_disjoint (M:Finset (LocalOrdinaryCycle Q F T r))
    (K:SimpleGraph V)
    (hK:∀ C∈M,∀ x∈localOrdinaryVertices C,∀ y∈localOrdinaryVertices C,¬K.Adj x y):
    Disjoint (localOrdinaryFactorGraph M) K:=by
  apply disjoint_iff_inf_le.mpr
  intro x y hxy
  obtain ⟨C,hC,hCxy⟩:=(localOrdinaryFactorGraph_adj M x y).mp hxy.1
  exact (hK C hC x (Set.mem_toFinset.mpr hCxy.mem_support_left)
    y (Set.mem_toFinset.mpr hCxy.mem_support_right) hxy.2).elim

theorem local_factor_graph_choice (Y:Finset V) (K:SimpleGraph V)
    (hfactor:∃ M:Finset (LocalOrdinaryCycle Q F T r),
      ((∀ C∈M,∀ D∈M,C≠D→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices D)) ∧
        M.biUnion localOrdinaryVertices=Y) ∧
      ∀ C∈M,∀ x∈localOrdinaryVertices C,∀ y∈localOrdinaryVertices C,¬K.Adj x y):
    ∃ M:Finset (LocalOrdinaryCycle Q F T r),
      ((∀ C∈M,∀ D∈M,C≠D→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices D)) ∧
        M.biUnion localOrdinaryVertices=Y) ∧
      localOrdinaryFactorGraph M≤spanningRestriction Q Y ∧
      (∀ v,(localOrdinaryFactorGraph M).degree v≤2) ∧
      Disjoint (localOrdinaryFactorGraph M) K:=by
  obtain ⟨M,hM,havoid⟩:=hfactor
  exact ⟨M,hM,localOrdinaryFactorGraph_restriction M Y hM.2,
    localOrdinaryFactorGraph_degree M hM.1,localOrdinaryFactorGraph_disjoint M K havoid⟩

end Oberwolfach
