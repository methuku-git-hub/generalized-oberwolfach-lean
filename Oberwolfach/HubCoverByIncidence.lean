module

public import Oberwolfach.HubIncidenceDegrees

@[expose] public section

/-! Successive hub factors with a row-incidence degree bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {Q F:SimpleGraph V} {H:V→U→Prop} {r n:ℕ}

theorem sequential_ordinary_hub_wheels_by_incidence (u : Fin n→U) (hu : Function.Injective u)
    (T : Fin n→Finset V) (hH : ∀ i,∀ v∈T i,H v (u i))
    (hfactor : ∀ i,∀ D : SimpleGraph V,(∀ v,D.degree v≤2*(Finset.univ.filter (fun i=>v∈T i)).card) →
      HasResourceDecomposition (localOrdinaryVertices (Q:=Q\D) (F:=F) (T:=T i) (r:=r)) (T i)) :
    ∃ M : Finset (OrdinaryWheel Q F H r),
      (∀ W∈M,∀ Z∈M,W≠Z → Disjoint (ordinaryWheelResources W) (ordinaryWheelResources Z)) ∧
      M.biUnion ordinaryWheelResources=(ordinaryWheelRimGraph M).edgeFinset.image Sum.inl ∪
        Finset.univ.biUnion (fun i=>(T i).image (fun v=>Sum.inr (v,u i))) ∧
      (∀ v,(ordinaryWheelRimGraph M).degree v≤2*(Finset.univ.filter (fun i=>v∈T i)).card) ∧
      (∀ i,∀ v∈T i,∃! W : M,Sum.inr (v,u i)∈ordinaryWheelResources W.val) := by
  let allowed:=fun (i : Fin n) (M : Finset (OrdinaryWheel Q F H r))=>
    (∀ W∈M,∀ Z∈M,W≠Z → Disjoint (ordinaryWheelResources W) (ordinaryWheelResources Z)) ∧
    M.biUnion ordinaryWheelResources=(ordinaryWheelRimGraph M).edgeFinset.image Sum.inl ∪
      (T i).image (fun v=>Sum.inr (v,u i)) ∧
    (∀ v,(ordinaryWheelRimGraph M).degree v≤2) ∧ (∀ W∈M,ordinaryWheelHub W=u i)
  let comp:=fun M N : Finset (OrdinaryWheel Q F H r)=>
    Disjoint (M.biUnion ordinaryWheelResources) (N.biUnion ordinaryWheelResources)
  obtain ⟨C,hC,hcross⟩:=sequential_select_prefix n allowed comp ∅ (by
    intro i A hA
    let D:=⨆ j,ordinaryWheelRimGraph (A j)
    have hdeg (j : Fin n) (v : V) : (ordinaryWheelRimGraph (A j)).degree v≤2 := by
      by_cases hj : j.val < i.val
      · exact (hA.2.1 j hj).2.2.1 v
      · rw [hA.1 j (by omega),ordinaryWheelRimGraph_empty];simp
    have hfuture (j : Fin n) (hj : i.val≤j.val) : ordinaryWheelRimGraph (A j)=⊥ := by
      rw [hA.1 j hj,ordinaryWheelRimGraph_empty]
    have hD (v:V):D.degree v≤2*(Finset.univ.filter (fun j=>v∈T j)).card:=by
      apply graph_family_degree_by_support (fun j=>ordinaryWheelRimGraph (A j)) T 2 v (fun j=>hdeg j v)
      intro j w hjw
      by_cases hj:j.val < i.val
      · exact ordinary_hub_packing_rim_support (A j) (T j) (u j) (hA.2.1 j hj).2.1 v w hjw
      · rw [hfuture j (by omega)] at hjw
        exact hjw.elim
    obtain ⟨M,hM,hunion,hdegM,hhub,havoid⟩:=ordinary_factor_wheels_avoiding D (T i) (u i) (hH i) (hfactor i D hD)
    refine ⟨M,⟨hM,hunion,hdegM,hhub⟩,?_⟩
    intro j hji
    apply ordinary_wheel_packings_disjoint (A j) M (u j) (u i)
      (fun h=>by have h':=congrArg Fin.val (hu h);omega) (hA.2.1 j hji).2.2.2 hhub
    exact (havoid.mono_right (le_iSup (fun j=>ordinaryWheelRimGraph (A j)) j)).symm)
  have hcross' (i j : Fin n) (hne : i≠j) :
      Disjoint ((C i).biUnion ordinaryWheelResources) ((C j).biUnion ordinaryWheelResources) := by
    rcases lt_or_gt_of_ne hne with hij|hji
    · exact hcross i j hij
    · exact (hcross j i hji).symm
  let M:=Finset.univ.biUnion C
  have hM : ∀ W∈M,∀ Z∈M,W≠Z → Disjoint (ordinaryWheelResources W) (ordinaryWheelResources Z) := by
    intro W hW Z hZ hne
    obtain ⟨i,_,hWi⟩:=Finset.mem_biUnion.mp hW
    obtain ⟨j,_,hZj⟩:=Finset.mem_biUnion.mp hZ
    by_cases hij : i=j
    · subst j;exact (hC i).1 W hWi Z hZj hne
    · exact (hcross' i j hij).mono
        (resource_subset_union ordinaryWheelResources (C i) W hWi)
        (resource_subset_union ordinaryWheelResources (C j) Z hZj)
  have hunion : M.biUnion ordinaryWheelResources=(ordinaryWheelRimGraph M).edgeFinset.image Sum.inl ∪
      Finset.univ.biUnion (fun i=>(T i).image (fun v=>Sum.inr (v,u i))) := by
    ext e
    cases e with
    | inl e =>
      have he:=(ordinaryWheelRimGraph_edges M e).symm
      simpa only [Finset.mem_biUnion,ordinaryWheelResources_rim,Finset.mem_union,
        Finset.mem_image,Sum.inl.injEq,Sum.inr_ne_inl,and_false,exists_false,or_false,
        SimpleGraph.mem_edgeFinset,exists_eq_right] using he
    | inr vu =>
      constructor
      · intro he
        obtain ⟨W,hW,he⟩:=Finset.mem_biUnion.mp he
        obtain ⟨i,_,hWi⟩:=Finset.mem_biUnion.mp hW
        have hi : Sum.inr vu∈(C i).biUnion ordinaryWheelResources:=Finset.mem_biUnion.mpr ⟨W,hWi,he⟩
        rw [(hC i).2.1] at hi
        have hsp : Sum.inr (α:=Sym2 V) vu∈(T i).image (fun v=>Sum.inr (v,u i)) := by
          rcases Finset.mem_union.mp hi with hi|hi
          · obtain ⟨e,_,he⟩:=Finset.mem_image.mp hi;cases he
          · exact hi
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hsp⟩)
      · intro he
        rcases Finset.mem_union.mp he with he|he
        · obtain ⟨e,_,he⟩:=Finset.mem_image.mp he;cases he
        · obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp he
          have hi' : Sum.inr vu∈(C i).biUnion ordinaryWheelResources:=by
            rw [(hC i).2.1];exact Finset.mem_union_right _ hi
          obtain ⟨W,hWi,he⟩:=Finset.mem_biUnion.mp hi'
          exact Finset.mem_biUnion.mpr ⟨W,Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hWi⟩,he⟩
  refine ⟨M,hM,hunion,?_,?_⟩
  · intro v
    rw [ordinaryWheelRimGraph_biUnion]
    exact graph_family_degree_by_support (fun i=>ordinaryWheelRimGraph (C i)) T 2 v
      (fun i=>(hC i).2.2.1 v)
      (fun i w hi=>ordinary_hub_packing_rim_support (C i) (T i) (u i) (hC i).2.1 v w hi)
  · intro i v hv
    apply resource_factor_vertex_unique ordinaryWheelResources M hM
    rw [hunion]
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨v,hv,rfl⟩⟩)

end Oberwolfach
