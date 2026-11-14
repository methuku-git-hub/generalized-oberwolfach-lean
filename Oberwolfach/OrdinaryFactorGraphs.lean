module

public import Oberwolfach.CycleVertexMatchingWeights
public import Oberwolfach.ResourceDecompositions
public import Oberwolfach.FractionalRelabeling

@[expose] public section

/-! Physical graphs of vertex-disjoint cycle families, and transport from
an induced vertex domain to the original graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  {G : SimpleGraph V} {Q : SimpleGraph W} {r : ℕ}

def ordinaryFactorGraph (M : Finset (OrdinaryCycle G r)) : SimpleGraph V :=
  ⨆ C ∈ M, C.val.val

theorem ordinaryFactorGraph_subhost (M : Finset (OrdinaryCycle G r)) :
    ordinaryFactorGraph M ≤ G := by
  exact iSup_le (fun C=>iSup_le (fun _=>C.property))

theorem ordinaryFactorGraph_support (M : Finset (OrdinaryCycle G r)) :
    (ordinaryFactorGraph M).support.toFinset=M.biUnion (ordinaryCycleVertices G r) := by
  ext v
  simp only [Set.mem_toFinset,SimpleGraph.mem_support,ordinaryFactorGraph,SimpleGraph.iSup_adj,
    Finset.mem_biUnion,ordinaryCycleVertices,Set.mem_toFinset]
  constructor
  · rintro ⟨w,C,hC,h⟩; exact ⟨C,hC,w,h⟩
  · rintro ⟨C,hC,w,h⟩; exact ⟨w,C,hC,h⟩

theorem ordinaryFactorGraph_degree_le_two (M : Finset (OrdinaryCycle G r))
    (hM : ∀ C∈M,∀ D∈M,C≠D → Disjoint (ordinaryCycleVertices G r C) (ordinaryCycleVertices G r D))
    (v : V) : (ordinaryFactorGraph M).degree v≤2 := by
  by_cases hv : v∈(ordinaryFactorGraph M).support
  · rw [SimpleGraph.mem_support] at hv
    obtain ⟨w,hw⟩:=hv
    change (⨆ C∈M,C.val.val).Adj v w at hw
    simp only [SimpleGraph.iSup_adj] at hw
    obtain ⟨C,hC,hcv⟩ := hw
    have he : (ordinaryFactorGraph M).neighborFinset v=C.val.val.neighborFinset v := by
      ext z
      simp only [SimpleGraph.mem_neighborFinset,ordinaryFactorGraph,SimpleGraph.iSup_adj]
      constructor
      · rintro ⟨D,hD,hd⟩
        have hDC : D=C := by
          by_contra hne
          exact (Finset.disjoint_left.mp (hM D hD C hC hne))
            (Set.mem_toFinset.mpr hd.mem_support_left) (Set.mem_toFinset.mpr hcv.mem_support_left)
        simpa only [hDC] using hd
      · intro hz;exact ⟨C,hC,hz⟩
    have hdeg : (ordinaryFactorGraph M).degree v=C.val.val.degree v := by
      rw [←SimpleGraph.card_neighborFinset_eq_degree,he,SimpleGraph.card_neighborFinset_eq_degree]
    rw [hdeg]
    rcases C.val.property.degree_zero_or_two v with h|h <;> omega
  · rw [(ordinaryFactorGraph M).degree_eq_zero_iff_notMem_support v |>.mpr hv]
    omega

def ordinaryCycleLift (f : W ↪ V) (hQ : Q.map f≤G) (C : OrdinaryCycle Q r) : OrdinaryCycle G r :=
  ⟨⟨C.val.val.map f,C.val.property.map f⟩,(SimpleGraph.map_monotone f C.property).trans hQ⟩

theorem ordinaryCycleLift_vertices (f : W ↪ V) (hQ : Q.map f≤G) (C : OrdinaryCycle Q r) :
    ordinaryCycleVertices G r (ordinaryCycleLift f hQ C)=(ordinaryCycleVertices Q r C).image f := by
  ext v
  simp only [ordinaryCycleVertices,ordinaryCycleLift,Set.mem_toFinset,SimpleGraph.support_map,
    Set.mem_image,Finset.mem_image,Set.mem_toFinset]

theorem ordinaryCycleLift_disjoint_edges (f : W ↪ V) (hQ : Q.map f≤G)
    (C D : OrdinaryCycle Q r) (hCD : Disjoint C.val.val.edgeFinset D.val.val.edgeFinset) :
    Disjoint (ordinaryCycleLift f hQ C).val.val.edgeFinset (ordinaryCycleLift f hQ D).val.val.edgeFinset := by
  have hh : Disjoint (C.val.val.map f).edgeFinset (D.val.val.map f).edgeFinset := by
    rw [SimpleGraph.edgeFinset_map,SimpleGraph.edgeFinset_map]
    exact (Finset.disjoint_map _).mpr hCD
  convert hh using 1 <;> congr!

theorem ordinary_cycle_family_lift (f : W ↪ V) (hQ : Q.map f≤G)
    (M : Finset (OrdinaryCycle Q r))
    (hM : ∀ C∈M,∀ D∈M,C≠D → Disjoint (ordinaryCycleVertices Q r C) (ordinaryCycleVertices Q r D)) :
    (∀ C∈M.image (ordinaryCycleLift f hQ),∀ D∈M.image (ordinaryCycleLift f hQ),C≠D →
      Disjoint (ordinaryCycleVertices G r C) (ordinaryCycleVertices G r D)) ∧
    (M.image (ordinaryCycleLift f hQ)).biUnion (ordinaryCycleVertices G r)=
      (M.biUnion (ordinaryCycleVertices Q r)).image f := by
  constructor
  · intro C hC D hD hne
    obtain ⟨C,hCM,rfl⟩:=Finset.mem_image.mp hC
    obtain ⟨D,hDM,rfl⟩:=Finset.mem_image.mp hD
    rw [ordinaryCycleLift_vertices,ordinaryCycleLift_vertices]
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hv
    obtain ⟨b,hb,he⟩:=Finset.mem_image.mp hw
    have hab:=f.injective he
    subst b
    exact (Finset.disjoint_left.mp (hM C hCM D hDM
      (fun h=>hne (congrArg (ordinaryCycleLift f hQ) h)))) ha hb
  · ext v
    constructor
    · intro hv
      obtain ⟨_,hC,hv⟩:=Finset.mem_biUnion.mp hv
      obtain ⟨C,hCM,rfl⟩:=Finset.mem_image.mp hC
      rw [ordinaryCycleLift_vertices] at hv
      obtain ⟨a,ha,he⟩:=Finset.mem_image.mp hv
      exact Finset.mem_image.mpr ⟨a,Finset.mem_biUnion.mpr ⟨C,hCM,ha⟩,he⟩
    · intro hv
      obtain ⟨a,ha,he⟩:=Finset.mem_image.mp hv
      obtain ⟨C,hC,ha⟩:=Finset.mem_biUnion.mp ha
      apply Finset.mem_biUnion.mpr
      refine ⟨ordinaryCycleLift f hQ C,Finset.mem_image.mpr ⟨C,hC,rfl⟩,?_⟩
      rw [ordinaryCycleLift_vertices]
      exact Finset.mem_image.mpr ⟨a,ha,he⟩

theorem ordinary_factor_lift (f : W ↪ V) (hQ : Q.map f≤G) (S : Finset W)
    (hS : HasResourceDecomposition (ordinaryCycleVertices Q r) S) :
    HasResourceDecomposition (ordinaryCycleVertices G r) (S.image f) := by
  obtain ⟨M,hM,hcover⟩:=hS
  refine ⟨M.image (ordinaryCycleLift f hQ),?_,?_⟩
  · intro C hC D hD hne
    obtain ⟨C,hCM,rfl⟩:=Finset.mem_image.mp hC
    obtain ⟨D,hDM,rfl⟩:=Finset.mem_image.mp hD
    rw [ordinaryCycleLift_vertices,ordinaryCycleLift_vertices]
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hv
    obtain ⟨b,hb,he⟩:=Finset.mem_image.mp hw
    have hab:=f.injective he
    subst b
    exact (Finset.disjoint_left.mp (hM C hCM D hDM (fun h=>hne (congrArg (ordinaryCycleLift f hQ) h)))) ha hb
  · rw [←hcover]
    ext v
    constructor
    · intro hv
      obtain ⟨_,hC,hv⟩:=Finset.mem_biUnion.mp hv
      obtain ⟨C,hCM,rfl⟩:=Finset.mem_image.mp hC
      rw [ordinaryCycleLift_vertices] at hv
      obtain ⟨a,ha,he⟩:=Finset.mem_image.mp hv
      exact Finset.mem_image.mpr ⟨a,Finset.mem_biUnion.mpr ⟨C,hCM,ha⟩,he⟩
    · intro hv
      obtain ⟨a,ha,he⟩:=Finset.mem_image.mp hv
      obtain ⟨C,hC,ha⟩:=Finset.mem_biUnion.mp ha
      apply Finset.mem_biUnion.mpr
      refine ⟨ordinaryCycleLift f hQ C,Finset.mem_image.mpr ⟨C,hC,rfl⟩,?_⟩
      rw [ordinaryCycleLift_vertices]
      exact Finset.mem_image.mpr ⟨a,ha,he⟩

theorem ordinary_factor_induced_lift (S : Finset V)
    (hS : HasResourceDecomposition (ordinaryCycleVertices (G.induce (S:Set V)) r) Finset.univ) :
    HasResourceDecomposition (ordinaryCycleVertices G r) S := by
  have hle : (G.induce (S:Set V)).map (Function.Embedding.subtype _)≤G := by
    intro v w h
    rw [SimpleGraph.map_adj] at h
    obtain ⟨a,b,hab,rfl,rfl⟩:=h
    exact hab
  have hh:=ordinary_factor_lift (Function.Embedding.subtype _) hle Finset.univ hS
  have he : Finset.univ.image (Function.Embedding.subtype (fun v=>v∈(S:Set V)))=S := by
    ext v
    constructor
    · intro hv
      obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hv
      exact a.property
    · intro hv
      exact Finset.mem_image.mpr ⟨⟨v,hv⟩,Finset.mem_univ _,rfl⟩
  simpa only [he] using hh

end Oberwolfach
