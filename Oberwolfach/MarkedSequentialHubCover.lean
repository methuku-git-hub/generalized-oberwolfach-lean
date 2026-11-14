module

public import Oberwolfach.MarkedHubFactorLift

@[expose] public section

/-! Successive marked hub factors form one physical wheel packing.
Each earlier hub contributes at most two to the deleted rim degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 22000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {m b n:ℕ} {π:Equiv.Perm V} {H₀ Hₖ:V→U→Prop}

theorem sequential_marked_hub_wheels (hm:1≤m) (hb:1≤b)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (u:Fin n→U) (hu:Function.Injective u)
    (hsep:∀ i v z,H₀ v (u i)→Hₖ z (u i)→v≠π z)
    (hfactor:∀ i,∀ D:SimpleGraph V,(∀ v,D.degree v≤2*n)→
      ∃ M:Finset (HubMarkedCycle (fun e:{e:E // ¬D.Adj (tail e) (head e)}=>tail e.val) (fun e=>head e.val)
        (fun e:{e:K // ¬D.Adj (ktail e) (π (khead e))}=>ktail e.val) (fun e=>khead e.val) m π b H₀ Hₖ (u i)),
        (∀ C∈M,∀ Z∈M,C≠Z→Disjoint (hubMarkedCycleVertices (u i) C) (hubMarkedCycleVertices (u i) Z))∧
        M.biUnion (hubMarkedCycleVertices (u i))=Finset.univ.filter (fun v=>H₀ v (u i)∨Hₖ v (u i))):
    ∃ M:Finset (MarkedWheel tail head ktail khead m π b H₀ Hₖ),
      (∀ W∈M,∀ Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))∧
      M.biUnion markedWheelPhysicalResources=(markedPackingRims M).image Sum.inl∪
        Finset.univ.biUnion (fun i=>(Finset.univ.filter (fun v=>H₀ v (u i)∨Hₖ v (u i))).image (fun v=>Sum.inr (v,u i)))∧
      (∀ v,(markedPackingRimGraph M).degree v≤2*n)∧
      (∀ i v,H₀ v (u i)∨Hₖ v (u i)→∃! W:M,Sum.inr (v,u i)∈markedWheelPhysicalResources W.val)∧
      (∀ e∈markedPackingRims M,e.card=2):=by
  let T:=fun i=>Finset.univ.filter (fun v=>H₀ v (u i)∨Hₖ v (u i))
  let allowed:=fun (i:Fin n) (M:Finset (MarkedWheel tail head ktail khead m π b H₀ Hₖ))=>
    (∀ W∈M,∀ Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))∧
    M.biUnion markedWheelPhysicalResources=(markedPackingRims M).image Sum.inl∪(T i).image (fun v=>Sum.inr (v,u i))∧
    (∀ v,(markedPackingRimGraph M).degree v≤2)∧(∀ W∈M,W.2.val=u i)∧(∀ e∈markedPackingRims M,e.card=2)
  let comp:=fun M N:Finset (MarkedWheel tail head ktail khead m π b H₀ Hₖ)=>
    Disjoint (M.biUnion markedWheelPhysicalResources) (N.biUnion markedWheelPhysicalResources)
  obtain ⟨C,hC,hcross⟩:=sequential_select_prefix n allowed comp ∅ (by
    intro i A hA
    let D:=⨆ j,markedPackingRimGraph (A j)
    have hdeg (j:Fin n) (v:V):(markedPackingRimGraph (A j)).degree v≤2:=by
      by_cases hj:j.val < i.val
      · exact (hA.2.1 j hj).2.2.1 v
      · rw [hA.1 j (by omega),markedPackingRimGraph_empty];simp
    have hfuture (j:Fin n) (hj:i.val≤j.val):markedPackingRimGraph (A j)=⊥:=by
      rw [hA.1 j hj,markedPackingRimGraph_empty]
    have hD (v:V):D.degree v≤2*n:=
      (graph_iSup_prefix_degree_bound (fun j=>markedPackingRimGraph (A j)) i 2 hdeg hfuture v).trans
        (Nat.mul_le_mul_left 2 (Nat.le_of_lt i.isLt))
    obtain ⟨F,hF,hcov⟩:=hfactor i D hD
    obtain ⟨M,hM,hunion,hdegM,hhub,hpairs,havoid⟩:=marked_hub_factor_wheels_avoiding (u i) hm hb hp (hsep i) D F hF hcov
    refine ⟨M,⟨hM,hunion,hdegM,hhub,hpairs⟩,?_⟩
    intro j hji
    apply marked_packing_distinct_hubs_disjoint (A j) M (u j) (u i)
      (fun h=>by have h':=congrArg Fin.val (hu h);omega) (hA.2.1 j hji).2.2.2.1 hhub (hA.2.1 j hji).2.2.2.2
    exact (havoid.mono_right (le_iSup (fun j=>markedPackingRimGraph (A j)) j)).symm)
  have hcross' (i j:Fin n) (hne:i≠j):
      Disjoint ((C i).biUnion markedWheelPhysicalResources) ((C j).biUnion markedWheelPhysicalResources):=by
    rcases lt_or_gt_of_ne hne with hij|hji
    · exact hcross i j hij
    · exact (hcross j i hji).symm
  let M:=Finset.univ.biUnion C
  have hM:∀ W∈M,∀ Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z):=by
    intro W hW Z hZ hne
    obtain ⟨i,_,hWi⟩:=Finset.mem_biUnion.mp hW
    obtain ⟨j,_,hZj⟩:=Finset.mem_biUnion.mp hZ
    by_cases hij:i=j
    · subst j;exact (hC i).1 W hWi Z hZj hne
    · exact (hcross' i j hij).mono
        (resource_subset_union markedWheelPhysicalResources (C i) W hWi)
        (resource_subset_union markedWheelPhysicalResources (C j) Z hZj)
  have hunion:M.biUnion markedWheelPhysicalResources=(markedPackingRims M).image Sum.inl∪
      Finset.univ.biUnion (fun i=>(T i).image (fun v=>Sum.inr (v,u i))):=by
    ext e
    cases e with
    | inl e=>
      simp only [Finset.mem_biUnion,markedWheelPhysicalResources_rim,Finset.mem_union,
        Finset.mem_image,Sum.inl.injEq,Sum.inr_ne_inl,and_false,exists_false,or_false,exists_eq_right,
        markedPackingRims,Finset.mem_univ,true_and]
    | inr e=>
      constructor
      · intro he
        obtain ⟨W,hW,he⟩:=Finset.mem_biUnion.mp he
        obtain ⟨i,_,hWi⟩:=Finset.mem_biUnion.mp hW
        have hi:Sum.inr e∈(C i).biUnion markedWheelPhysicalResources:=Finset.mem_biUnion.mpr ⟨W,hWi,he⟩
        rw [(hC i).2.1] at hi
        have hsp:Sum.inr (α:=Finset V) e∈(T i).image (fun v=>Sum.inr (v,u i)):=by
          rcases Finset.mem_union.mp hi with hi|hi
          · obtain ⟨x,_,he⟩:=Finset.mem_image.mp hi;cases he
          · exact hi
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hsp⟩)
      · intro he
        rcases Finset.mem_union.mp he with he|he
        · obtain ⟨x,_,he⟩:=Finset.mem_image.mp he;cases he
        · obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp he
          have hi':Sum.inr e∈(C i).biUnion markedWheelPhysicalResources:=by
            rw [(hC i).2.1];exact Finset.mem_union_right _ hi
          obtain ⟨W,hWi,he⟩:=Finset.mem_biUnion.mp hi'
          exact Finset.mem_biUnion.mpr ⟨W,Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hWi⟩,he⟩
  refine ⟨M,hM,hunion,?_,?_,?_⟩
  · intro v
    rw [markedPackingRimGraph_biUnion]
    have hh:=graph_iSup_local_degree_bound (fun i=>markedPackingRimGraph (C i)) Finset.univ v 2
      (fun i=>(hC i).2.2.1 v)
    simp only [Finset.inter_univ,SimpleGraph.card_neighborFinset_eq_degree] at hh
    exact hh.trans (Nat.mul_le_mul_left 2 (by simpa using (Finset.card_filter_le (s:=Finset.univ)
      (p:=fun i=>∃ w∈(Finset.univ:Finset V),(markedPackingRimGraph (C i)).Adj v w))))
  · intro i v hv
    apply resource_factor_vertex_unique markedWheelPhysicalResources M hM
    rw [hunion]
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,
      Finset.mem_image.mpr ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩,rfl⟩⟩)
  · intro e he
    obtain ⟨W,hW,he⟩:=Finset.mem_biUnion.mp he
    obtain ⟨i,_,hWi⟩:=Finset.mem_biUnion.mp hW
    exact (hC i).2.2.2.2 e (Finset.mem_biUnion.mpr ⟨W,hWi,he⟩)

end Oberwolfach
