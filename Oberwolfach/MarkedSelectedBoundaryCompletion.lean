module

public import Oberwolfach.MarkedBoundaryPackingFromAssignments
public import Oberwolfach.MarkedSelectedHubPacking
public import Oberwolfach.MarkedPackingUnions

@[expose] public section

/-! Complete the marked boundary from the selected physical factors and
actual endpoint assignments. Boundary paths use inner hubs; the selected
factors use outside hubs. All shared rim edges are explicitly excluded. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1800000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E T J I:Type} [Fintype V] [Fintype U] [Fintype J] [Fintype I]
    [DecidableEq V] [DecidableEq U] [DecidableEq J] [DecidableEq I]
    {tail head:E→V} {ktail khead:T→V} {H₀ HK:V→U→Prop}
    {π:Equiv.Perm V} {b l:ℕ} {c:ℝ}

theorem marked_selected_boundary_completion
    (X:Finset V) (Q:MarkedBoundaryExtensionCounts tail head ktail khead H₀ HK X c)
    (hl:2≤l) (hb:1≤b) (hphys:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hX:∀ x,π x∈X↔x∈X) (root:J↪V) (hrootX:∀ j,root j∉X)
    (A₀ A₁ X₀ X₁:J→Finset V) (Y₀ Y₁:J→Finset U)
    (P:∀ j,MarkedEndpointPairing (A₀ j) (A₁ j) (X₀ j) (X₁ j) (Y₀ j) (Y₁ j) H₀ HK π b)
    (hcross:∀ j k,j≠k→Disjoint (P j).graph (P k).graph)
    (incoming:∀ j,(A₀ j⊕A₁ j)↪E⊕T) (outgoing:∀ j,(X₀ j⊕X₁ j)↪E⊕T)
    (hinhead:∀ j a,Sum.elim head khead (incoming j a)=root j)
    (hintail:∀ j a,Sum.elim tail ktail (incoming j a)=taggedSubsetValue (A₀ j) (A₁ j) a)
    (houttail:∀ j a,Sum.elim tail ktail (outgoing j a)=root j)
    (houthead:∀ j a,Sum.elim head khead (outgoing j a)=taggedSubsetValue (X₀ j) (X₁ j) a)
    (hintype:∀ j a,(incoming j a).isRight=a.isRight)
    (houttype:∀ j a,(outgoing j a).isRight=a.isRight)
    (hAX:∀ j,A₀ j∪A₁ j⊆X) (hXX:∀ j,X₀ j∪X₁ j⊆X)
    (hsepA:∀ j a,a∈A₀ j∪A₁ j→¬PermutationClose π b a (root j))
    (hsepX:∀ j a,a∈X₀ j∪X₁ j→¬PermutationClose π b a (root j))
    (hY₀:∀ j u,u∈Y₀ j→H₀ (root j) u) (hY₁:∀ j u,u∈Y₁ j→HK (root j) u)
    (D K:ℕ) (hK:0<K) (hdeg:∀ w,(⨆ j,(P j).graph).degree w≤D)
    (Z:Finset U) (hYZ:∀ j,Y₀ j∪Y₁ j⊆Z)
    (hub:I↪U) (houtside:∀ j,hub j∉Z) (Y:I→Finset V) (hYX:∀ j,Y j⊆X)
    (F:∀ j,MarkedHubFactorOn tail head ktail khead (l+3) π b H₀ HK (hub j) (Y j))
    (hFcross:∀ j k,j≠k→Disjoint (F j).rim (F k).rim)
    (hFsep:∀ j v z,H₀ v (hub j)→HK z (hub j)→v≠π z)
    (δ:ℝ) (hδ:0≤δ) (hG:∀ v,((⨆ j,(F j).rim).degree v:ℝ)≤δ)
    (hbudget:(Fintype.card (Σ j,Y₀ j⊕Y₁ j)*(l+4):ℕ)/(K:ℝ)+D+(D*(l+4):ℕ)+
      (l+5)*(2*b+1)+2*(δ+4*(K+D:ℕ))<c):
    ∃ M:Finset (MarkedWheel tail head ktail khead (l+3) π b H₀ HK),
      (∀ W∈M,∀ W'∈M,W≠W'→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources W'))∧
      (∀ j a,Sum.inl (markedPhysicalEdge tail head ktail khead π (incoming j a))∈M.biUnion markedWheelPhysicalResources)∧
      (∀ j a,Sum.inl (markedPhysicalEdge tail head ktail khead π (outgoing j a))∈M.biUnion markedWheelPhysicalResources)∧
      (∀ j u,u∈Y₀ j∪Y₁ j→Sum.inr (root j,u)∈M.biUnion markedWheelPhysicalResources)∧
      (∀ j x,x∈Y j→Sum.inr (x,hub j)∈M.biUnion markedWheelPhysicalResources)∧
      (∀ v,((spanningRestriction (markedPackingRimGraph M) X).degree v:ℝ)≤δ+4*(K+D:ℕ))∧
      (∀ v∈X,(Z.filter (markedPackingSpokes M v)).card≤K+D)∧
      (∀ u∈Z,(Finset.univ.filter (fun v=>markedPackingSpokes M v u)).card≤D*(l+4))∧
      (∀ B:Finset (Finset V⊕(V×U)),
        (∀ e∈B,¬markedInnerResource X Z e)→
        (∀ j a,Sum.inl (markedPhysicalEdge tail head ktail khead π (incoming j a))∉B)→
        (∀ j a,Sum.inl (markedPhysicalEdge tail head ktail khead π (outgoing j a))∉B)→
        (∀ j u,u∈Y₀ j∪Y₁ j→Sum.inr (root j,u)∉B)→
        (∀ j x,x∈Y j→Sum.inr (x,hub j)∉B)→
        Disjoint (M.biUnion markedWheelPhysicalResources) B) := by
  let G:SimpleGraph V:=⨆ j,(F j).rim
  have hGX:GraphSupportedOn X G:=by
    intro v w hvw
    obtain ⟨j,hj⟩:=SimpleGraph.iSup_adj.mp hvw
    have hs:=marked_factor_physical_supported (hub j) (F j).cycles (Y j) (F j).covers v w hj
    have hsub:Y j∪(Y j).image π⊆X:=by
      intro a ha
      rcases Finset.mem_union.mp ha with ha|ha
      · exact hYX j ha
      · obtain ⟨w,hw,he⟩:=Finset.mem_image.mp ha
        rw [←he]
        exact (hX w).mpr (hYX j hw)
    exact ⟨hsub hs.1,hsub hs.2⟩
  obtain ⟨Mh,hMh,hMhr,hMhs,hMhrows⟩:=marked_selected_hub_packing hub Y (by omega:1≤l+3) hb hphys hFsep F hFcross
  obtain ⟨C,hC,hinc,hout,hroot,havoid,hrim,hrow,hcol,hwhere,hclass⟩:=
    marked_boundary_packing_from_assignments X Q hl hb hphys hX root hrootX
      A₀ A₁ X₀ X₁ Y₀ Y₁ P hcross incoming outgoing hinhead hintail houttail houthead hintype houttype
      hAX hXX hsepA hsepX hY₀ hY₁ D K hK hdeg G hGX δ hδ hG hbudget
  let Mp:=Finset.univ.image C
  have hMp:∀ W∈Mp,∀ W'∈Mp,W≠W'→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources W'):=by
    intro W hW W' hW' hne
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hW
    obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hW'
    exact hC i j (fun he=>hne (congrArg C he))
  have hMr:markedPackingRimGraph Mp=markedFamilyRim C:=marked_family_image_rim C
  have hMs:markedPackingSpokes Mp=markedFamilySpokes C:=marked_family_image_spokes C
  have havoid':Disjoint (markedPackingRimGraph Mp) (markedPackingRimGraph Mh):=by
    rw [hMr,hMhr]
    apply disjoint_iff_inf_le.mpr
    intro a z haz
    obtain ⟨i,hi⟩:=SimpleGraph.iSup_adj.mp haz.1
    exact (disjoint_graphs_no_common_edge _ _ (havoid i) a z hi haz.2).elim
  have hcross':Disjoint (Mp.biUnion markedWheelPhysicalResources) (Mh.biUnion markedWheelPhysicalResources):=by
    apply marked_packings_disjoint_of_rims_and_hubs (by omega:1≤l+3) hb Mp Mh havoid'
    intro W hW W' hW' he
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hW
    obtain ⟨j,hj,_⟩:=hwhere i
    obtain ⟨k,hk,_⟩:=hMhrows W' hW'
    exact houtside k ((he.trans hk) ▸ hYZ j hj)
  let M:=Mh∪Mp
  have hres: M.biUnion markedWheelPhysicalResources=
      Mh.biUnion markedWheelPhysicalResources∪Mp.biUnion markedWheelPhysicalResources:=Finset.union_biUnion
  have hsp (v:V) (u:U):markedPackingSpokes M v u↔markedPackingSpokes Mh v u∨markedPackingSpokes Mp v u:=markedPackingSpokes_union Mh Mp v u
  have hhubout (v:V) (u:U) (hu:u∈Z):¬markedPackingSpokes Mh v u:=by
    intro hh
    obtain ⟨j,hj,_⟩:=(hMhs v u).mp hh
    exact houtside j (hj.symm ▸ hu)
  have hR:markedPackingRimGraph M=G⊔markedFamilyRim C:=by
    have he:markedPackingRimGraph M=markedPackingRimGraph Mh⊔markedPackingRimGraph Mp:=
      markedPackingRimGraph_union Mh Mp
    rw [he,hMr,hMhr]
  refine ⟨M,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro W hW W' hW' hne
    rcases Finset.mem_union.mp hW with hW|hW <;> rcases Finset.mem_union.mp hW' with hW'|hW'
    · exact hMh W hW W' hW' hne
    · exact hcross'.symm.mono (resource_subset_union _ _ W hW) (resource_subset_union _ _ W' hW')
    · exact hcross'.mono (resource_subset_union _ _ W hW) (resource_subset_union _ _ W' hW')
    · exact hMp W hW W' hW' hne
  · intro j a
    obtain ⟨i,hi⟩:=hinc j a
    rw [hres]
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨C i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,hi⟩)
  · intro j a
    obtain ⟨i,hi⟩:=hout j a
    rw [hres]
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨C i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,hi⟩)
  · intro j u hu
    obtain ⟨i,hi⟩:=hroot j u hu
    rw [hres]
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨C i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,hi⟩)
  · intro j x hx
    obtain ⟨W,hW,hh,hx⟩:=(hMhs x (hub j)).mpr ⟨j,rfl,hx⟩
    rw [hres]
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨W,hW,(markedWheelPhysicalResources_spoke W _ _).mpr ⟨hh,hx⟩⟩)
  · intro v
    rw [hR]
    have hle:spanningRestriction (G⊔markedFamilyRim C) X≤G⊔spanningRestriction (markedFamilyRim C) X:=by
      intro x y hxy
      obtain ⟨hg,hx,hy⟩:=(spanningRestriction_adj _ _ _ _).mp hxy
      exact hg.elim Or.inl (fun h=>Or.inr ((spanningRestriction_adj _ _ _ _).mpr ⟨h,hx,hy⟩))
    have hd:=((SimpleGraph.degree_le_of_le hle).trans
      (graph_degree_sup_le G (spanningRestriction (markedFamilyRim C) X) v)).trans
      (Nat.add_le_add_left (hrim v) (G.degree v))
    have hd':((spanningRestriction (G⊔markedFamilyRim C) X).degree v:ℝ)≤(G.degree v:ℝ)+(4*(K+D):ℕ):=by exact_mod_cast hd
    push_cast at hd' ⊢
    have hg:(G.degree v:ℝ)≤δ:=hG v
    linarith only [hd',hg]
  · intro v hv
    apply le_trans _ (hrow v hv)
    apply Finset.card_le_card
    intro u hu
    obtain ⟨hu,hvu⟩:=Finset.mem_filter.mp hu
    have hp:markedPackingSpokes Mp v u:=((hsp v u).mp hvu).resolve_left (hhubout v u hu)
    rw [hMs] at hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩
  · intro u hu
    apply le_trans _ (hcol u)
    apply Finset.card_le_card
    intro v hv
    have hp:markedPackingSpokes Mp v u:=((hsp v u).mp (Finset.mem_filter.mp hv).2).resolve_left (hhubout v u hu)
    rw [hMs] at hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩

  · intro B hB hiB hoB hrB hhB
    apply Finset.disjoint_left.mpr
    intro edge hedge hBedge
    obtain ⟨W,hW,hedge⟩:=Finset.mem_biUnion.mp hedge
    cases edge with
    | inl edge=>
      have hedge:=(markedWheelPhysicalResources_rim W edge).mp hedge
      rcases Finset.mem_union.mp hW with hW|hW
      · obtain ⟨j,_,hrows⟩:=hMhrows W hW
        obtain ⟨i,_,he⟩:=Finset.mem_image.mp hedge
        apply hB _ hBedge
        change edge⊆X
        rw [←he]
        simp only [Function.comp_apply]
        rw [marked_cycle_edge_inside_iff X hX]
        constructor
        · exact hYX j (hrows (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))
        · exact hYX j (hrows (Finset.mem_image.mpr ⟨finRotate (l+4) i,Finset.mem_univ _,rfl⟩))
      · obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hW
        rcases hclass i edge hedge with hin|⟨j,a,he⟩|⟨j,a,he⟩
        · exact hB _ hBedge hin
        · exact hiB j a (he ▸ hBedge)
        · exact hoB j a (he ▸ hBedge)
    | inr z=>
      have hh:=(markedWheelPhysicalResources_spoke W z.1 z.2).mp hedge
      rcases Finset.mem_union.mp hW with hW|hW
      · obtain ⟨j,hj,hrows⟩:=hMhrows W hW
        have hz:z.2=hub j:=hh.1.symm.trans hj
        exact hhB j z.1 (hrows hh.2) (hz ▸ hBedge)
      · obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hW
        obtain ⟨j,hj,hrows⟩:=hwhere i
        have hhub:z.2∈Y₀ j∪Y₁ j:=hh.1 ▸ hj
        rcases Finset.mem_insert.mp (hrows hh.2) with hx|hx
        · exact hrB j z.2 hhub (hx ▸ hBedge)
        · exact hB _ hBedge ⟨hx,hYZ j hhub⟩

end Oberwolfach
