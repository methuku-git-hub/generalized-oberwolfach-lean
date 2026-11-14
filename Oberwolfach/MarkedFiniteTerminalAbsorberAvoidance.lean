module

public import Oberwolfach.MarkedFiniteAbsorberProperty
public import Oberwolfach.MarkedSupportedResourceBounds
public import Oberwolfach.FiniteDisjointChoices
public import Oberwolfach.AlternativeAbsorberAssembly

@[expose] public section

/-! Finite terminal alternatives have bounded support, but the excluded
row and hub sets may be larger. The size bound is imposed separately on
each alternative, not on the excluded sets. The absorbers avoid every
resource internal to the larger excluded pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K I:Type} [Fintype V] [Fintype U] [Fintype I]
  [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K] [DecidableEq I]

theorem marked_finite_terminal_absorber_avoiding
    (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V) (H₀ HK:V→U→Prop)
    (b l s a₀ b₀ f:ℕ) (ε:ℝ)
    (habs:MarkedFiniteAbsorberProperty tail head ktail khead H₀ HK π b l ε s a₀ b₀ f)
    (X:Finset V) (Z:Finset U) (F₀:Finset (Finset V⊕(V×U)))
    (hX:(X.card:ℝ)≤ε*Fintype.card V+f) (hZ:(Z.card:ℝ)≤ε*Fintype.card V+f)
    (hbudget:F₀.card+Fintype.card I*(2*a₀^2+a₀*b₀)≤f)
    (A:I→Finset (E⊕K)) (S:I→Finset (V×U))
    (hsize:∀ i,(markedRemainderRows tail head ktail khead (A i) (S i)).card+
      (markedRemainderHubs (S i)).card≤s)
    (hdiv:∀ i,MarkedRemainderDivisible tail head ktail khead HK (A i) (S i) (l+4))
    (hrow:∀ i,markedRemainderRows tail head ktail khead (A i) (S i)⊆X)
    (hhub:∀ i,markedRemainderHubs (S i)⊆Z)
    (hsp:∀ i z,z∈S i→H₀ z.1 z.2∨HK z.1 z.2):
    ∃ C:MarkedSupportedEdgeSet tail head ktail khead π U,
      Disjoint C.edges F₀∧C.edges.card≤Fintype.card I*(2*a₀^2+a₀*b₀)∧
      C.rows.card≤Fintype.card I*a₀∧C.hubs.card≤Fintype.card I*b₀∧
      (∀ e∈C.edges,¬MarkedOldResource tail head ktail khead π X Z e)∧
      HasResourceDecomposition
        (fun W:MarkedWheel tail head ktail khead (l+4) π b H₀ HK=>markedWheelPhysicalResources W) C.edges∧
      ∀ i,IsResourceAbsorber
        (fun W:MarkedWheel tail head ktail khead (l+4) π b H₀ HK=>markedWheelPhysicalResources W)
        ((A i).image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪(S i).image Sum.inr) C.edges := by
  let R:=fun W:MarkedWheel tail head ktail khead (l+4) π b H₀ HK=>markedWheelPhysicalResources W
  let L:=fun i=>(A i).image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪(S i).image Sum.inr
  let d:=2*a₀^2+a₀*b₀
  let Good:=fun i (C:MarkedSupportedEdgeSet tail head ktail khead π U)=>
    IsResourceAbsorber R (L i) C.edges∧C.rows.card≤a₀∧C.hubs.card≤b₀∧
      ∀ e∈C.edges,¬MarkedOldResource tail head ktail khead π X Z e
  have chooseOne (i:I) (B:Finset (Finset V⊕(V×U)))
      (hB:B.card≤F₀.card+Fintype.card I*d):
      ∃ C,Good i C∧C.edges.card≤d∧Disjoint C.edges B:=by
    let B':=B.filter (fun e=>match e with | Sum.inl a=>a.card≤2 | Sum.inr _=>True)
    have hBf:B'.card≤f:=(Finset.card_filter_le _ _).trans (hB.trans hbudget)
    have hpair (e:Finset V) (he:Sum.inl e∈B'):e.card≤2:=(Finset.mem_filter.mp he).2
    obtain ⟨C,hC,havoid,hCr,hCh,_hrows,_hhubs,hOld,_hsep,_hrootsep⟩:=
      habs (A i) (S i) (hdiv i) (hsize i) (hsp i) X Z B' hBf hpair (hhub i) hZ hX
    have hOld':∀ e∈C.edges,¬MarkedOldResource tail head ktail khead π X Z e:=by
      intro e he ho
      exact hOld e he (marked_old_resource_mono Finset.subset_union_left (Finset.Subset.refl _) e ho)
    refine ⟨C,⟨hC,hCr,hCh,hOld'⟩,marked_supported_edges_card C a₀ b₀ hCr hCh,?_⟩
    apply Finset.disjoint_left.mpr
    intro e he hBe
    apply Finset.disjoint_left.mp havoid he
    apply Finset.mem_filter.mpr
    refine ⟨hBe,?_⟩
    cases e with
    | inl e=>exact marked_supported_rim_pair C e he
    | inr e=>trivial
  obtain ⟨C,hC,hCC⟩:=finite_disjoint_choices
    (fun C:MarkedSupportedEdgeSet tail head ktail khead π U=>C.edges) Good F₀ d chooseOne
  let Aall:=Finset.univ.biUnion (fun i=>(C i).edges)
  let Xall:=Finset.univ.biUnion (fun i=>(C i).rows)
  let Zall:=Finset.univ.biUnion (fun i=>(C i).hubs)
  let C₀:MarkedSupportedEdgeSet tail head ktail khead π U:=
    ⟨Xall,Zall,Aall,by
      intro e he
      obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp he
      exact marked_old_resource_mono
        (resource_subset_union (fun i=>(C i).rows) Finset.univ i (Finset.mem_univ _))
        (resource_subset_union (fun i=>(C i).hubs) Finset.univ i (Finset.mem_univ _)) e ((C i).supported e hi)⟩
  have hOldall:∀ e∈C₀.edges,¬MarkedOldResource tail head ktail khead π X Z e:=by
    intro e he
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp he
    exact (hC i).1.2.2.2 e hi
  have hLold (i:I) (e:Finset V⊕(V×U)) (he:e∈L i):
      MarkedOldResource tail head ktail khead π X Z e:=by
    rcases Finset.mem_union.mp he with he|he
    · obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp he
      refine ⟨a,rfl,hrow i ?_,hrow i ?_⟩
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,ha,rfl⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a,ha,rfl⟩))
    · obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp he
      exact ⟨hrow i (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z,hz,rfl⟩)),
        hhub i (Finset.mem_image.mpr ⟨z,hz,rfl⟩)⟩
  have hAX (i j:I):Disjoint (C i).edges (L j):=by
    apply Finset.disjoint_left.mpr
    intro e he hl
    exact (hC i).1.2.2.2 e he (hLold j e hl)
  have hall:=alternative_absorber_union R L (fun i=>(C i).edges) (fun i=>(hC i).1.1) hCC hAX
  refine ⟨C₀,?_,?_,?_,?_,hOldall,hall.1,hall.2⟩
  · apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp he
    exact Finset.disjoint_left.mp (hC i).2.2 hi hf
  · exact (Finset.card_biUnion_le_card_mul Finset.univ (fun i=>(C i).edges) d (by intro i _;exact (hC i).2.1)).trans_eq (by simp [d])
  · exact (Finset.card_biUnion_le_card_mul Finset.univ (fun i=>(C i).rows) a₀ (by intro i _;exact (hC i).1.2.1)).trans_eq (by simp [d])
  · exact (Finset.card_biUnion_le_card_mul Finset.univ (fun i=>(C i).hubs) b₀ (by intro i _;exact (hC i).1.2.2.1)).trans_eq (by simp [d])

end Oberwolfach
