module

public import Oberwolfach.MarkedFiveSeparatedHostRealizations
public import Oberwolfach.MarkedFiveSetSeparation
public import Oberwolfach.MarkedFourDiagramInputs
public import Oberwolfach.MarkedFiveGraphGeometry

@[expose] public section

/-! The actual five-graph marked absorber diagram, with four transformer
inputs. Graphs are constructed from host counts; their existence is not
an additional premise. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 48000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K A' S':Type} [Fintype V] [Fintype U] [Fintype A'] [Fintype S']
    [DecidableEq V] [DecidableEq U]

structure MarkedHostDiagram (m M:ℕ) (tail head:E→V) (ktail khead:K→V)
    (H₀ HK:V→U→Prop) (π:Equiv.Perm V) (b:ℕ)
    (original:Finset (Finset V⊕(V×U))) (W Z:Finset V) (B₀:Finset U)
    (oldRows:Finset V) (oldHubs:Finset U) (A' S':Type) [Fintype A'] [Fintype S'] where
  rows:Finset V
  hubs:Finset U
  original_rows:oldRows⊆rows
  original_hubs:oldHubs⊆hubs
  rows_card:rows.card≤5*M
  hubs_card:hubs.card≤5*M
  rows_avoid:∀ v∈rows,v∈W∪Z→v∈oldRows
  hubs_avoid:∀ u∈hubs,u∈B₀→u∈oldHubs
  rows_separated:∀ v∈rows\oldRows,∀ w∈rows\oldRows,v≠w→¬PermutationClose π b v w
  rows_root_separated:∀ v∈rows\oldRows,∀ w∈Z,¬PermutationClose π b v w
  D:Fin 5→Finset (Finset V⊕(V×U))
  disjoint:∀ i j,i≠j→Disjoint (D i) (D j)
  supported:∀ i,∀ e∈D i,MarkedOldResource tail head ktail khead π rows hubs e
  avoid:∀ i,i≠0→∀ e∈D i,¬MarkedOldResource tail head ktail khead π (W∪Z) B₀ e
  extra:Finset (Finset V⊕(V×U))
  first:D 0=original∪extra
  first_disjoint:Disjoint original extra
  extra_decomp:HasResourceDecomposition (fun C:MarkedWheel tail head ktail khead m π b H₀ HK=>markedWheelPhysicalResources C) extra
  extra_avoid:∀ e∈extra,¬MarkedOldResource tail head ktail khead π (W∪Z) B₀ e
  last_decomp:HasResourceDecomposition (fun C:MarkedWheel tail head ktail khead m π b H₀ HK=>markedWheelPhysicalResources C) (D 4)
  P:Fin 4→MarkedRootPair tail head ktail khead H₀ HK π b m A' S'
  source:∀ j,(P j).source=![D 1,D 1,D 3,D 3] j
  image:∀ j,(P j).image=![D 0,D 2,D 2,D 4] j
  roots:∀ j,(P j).R∪(P j).R'⊆rows
  baseHubs:∀ j,(P j).B=B₀∪hubs

variable {V₀ U₀ A S:Type} [Fintype V₀] [Fintype U₀] [Fintype A] [Fintype S]
    [DecidableEq V₀] [DecidableEq U₀] [DecidableEq A] [DecidableEq S]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ} {c ch:ℝ}

theorem marked_host_diagram
    (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (hl:2≤l) (G:IndexedMarkedGraph V₀ U₀ A S) (hG:G.IsBalanced (l+4))
    (R₀:IndexedMarkedHostRealization G tail head ktail khead H₀ HK π b)
    (n e:ℕ) (hn:Fintype.card V₀+Fintype.card U₀≤n) (he:Fintype.card A+Fintype.card S≤e)
    (v₀:V) (W Z:Finset V) (B:Finset U) (hr:∀ v,R₀.rows v∈Z) (hh:∀ u,R₀.hubs u∈B)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hbudget:(W.card:ℝ)+(Z.card+6*markedDiagramSize l n e+l+16)*(2*b+1)<c)
    (hB:(B.card:ℝ)+6*markedDiagramSize l n e<ch):
    Nonempty (MarkedHostDiagram (l+4) (markedDiagramSize l n e) tail head ktail khead H₀ HK π b
      R₀.resources W Z B R₀.rowSet R₀.hubSet (A⊕((A⊕S)×Fin (l+5))) (S⊕((A⊕S)×Fin (l+5)))):=by
  obtain ⟨L,extra,hpart,hpartdis,hextra,hextraOld,hLold,hLhub,hOldRows,hOldHubs,hLeftSep,hLeftNew,R,hRhub,hRrow,hRdec,hRightSep,T,hT,hTT⟩:=
    marked_five_host_realizations_separated Q hl G hG R₀ n e hn he v₀ W Z B hr hh hp hbudget hB
  let X:=ordinaryFiveUnion L.rowSet R.rowSet (fun i=>(T i).rowSet)
  let Y:=ordinaryFiveUnion L.hubSet R.hubSet (fun i=>(T i).hubSet)
  have hLT (i:Fin 3):Disjoint (T i).rowSet L.rowSet:=by
    apply Finset.disjoint_left.mpr
    intro v hv hvL
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hv
    exact ((hT i).2.2.2.1 a).2.1 (Finset.mem_union_left _ (Finset.mem_union_right _ hvL))
  have hRT (i:Fin 3):Disjoint (T i).rowSet R.rowSet:=by
    apply Finset.disjoint_left.mpr
    intro v hv hvR
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hv
    exact ((hT i).2.2.2.1 a).2.1 (Finset.mem_union_right _ hvR)
  have hLTB (i:Fin 3):Disjoint (T i).hubSet L.hubSet:=by
    apply Finset.disjoint_left.mpr
    intro v hv hvL
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hv
    exact (hT i).2.2.1 a (Finset.mem_union_left _ (Finset.mem_union_right _ hvL))
  have hRTB (i:Fin 3):Disjoint (T i).hubSet R.hubSet:=by
    apply Finset.disjoint_left.mpr
    intro v hv hvR
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hv
    exact (hT i).2.2.1 a (Finset.mem_union_right _ hvR)
  have hLR:Disjoint L.rowSet R.rowSet:=by
    apply Finset.disjoint_right.mpr
    intro v hv hvL
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hv
    exact (hRrow a).2.1 (Finset.mem_union_right _ hvL)
  have hLs (i:Fin 3):∀ v∈(T i).rowSet,∀ w∈L.rowSet,¬PermutationClose π b v w:=by
    intro v hv w hw
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hv
    exact ((hT i).2.2.2.1 a).2.2 w (Finset.mem_union_left _ (Finset.mem_union_right _ hw))
  have hRs (i:Fin 3):∀ v∈(T i).rowSet,∀ w∈R.rowSet,¬PermutationClose π b v w:=by
    intro v hv w hw
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hv
    exact ((hT i).2.2.2.1 a).2.2 w (Finset.mem_union_right _ hw)
  obtain ⟨P,hsource,himage,hProots,hProots',hPB⟩:=marked_four_diagram_inputs G hG L R T
    (fun i=>⟨(hT i).1,(hT i).2.1⟩) (fun i=>⟨hLT i,hLTB i⟩) (fun i=>⟨hRT i,hRTB i⟩)
    hLs hRs hTT (B∪Y)
    ((ordinaryFiveUnion_left _ _ _).trans Finset.subset_union_right)
    ((ordinaryFiveUnion_right _ _ _).trans Finset.subset_union_right)
    (fun i=>(ordinaryFiveUnion_mid L.hubSet R.hubSet (fun j=>(T j).hubSet) i).trans Finset.subset_union_right)
  have hgeom:=marked_five_graph_geometry L R T hp hLR (fun i=>(hLT i).symm) (fun i=>(hRT i).symm) (fun i j hij=>(hTT i j hij).1)
  have hXsep:∀ v∈X\R₀.rowSet,∀ w∈X\R₀.rowSet,v≠w→¬PermutationClose π b v w:=by
    apply marked_five_sets_separated π b L.rowSet R.rowSet (fun i=>(T i).rowSet) R₀.rowSet
    · intro v hv w hw hne
      obtain ⟨av,_,rfl⟩:=Finset.mem_image.mp (Finset.mem_sdiff.mp hv).1
      obtain ⟨aw,_,rfl⟩:=Finset.mem_image.mp (Finset.mem_sdiff.mp hw).1
      exact hLeftNew av aw (Finset.mem_sdiff.mp hv).2 (Finset.mem_sdiff.mp hw).2 hne
    · intro v hv w hw hne
      obtain ⟨av,_,rfl⟩:=Finset.mem_image.mp hv
      obtain ⟨aw,_,rfl⟩:=Finset.mem_image.mp hw
      exact hRightSep av aw hne
    · intro i v hv w hw hne
      obtain ⟨av,_,rfl⟩:=Finset.mem_image.mp hv
      obtain ⟨aw,_,rfl⟩:=Finset.mem_image.mp hw
      exact (hT i).2.2.2.2 av aw (fun he=>hne (congrArg (T i).rows he))
    · intro v hv w hw hc
      obtain ⟨aw,_,rfl⟩:=Finset.mem_image.mp hw
      exact (hRrow aw).2.2 v (Finset.mem_union_right _ hv) ((permutationClose_symm π b _ _).mp hc)
    · intro i v hv w hw hc;exact hLs i w hw v hv ((permutationClose_symm π b _ _).mp hc)
    · intro i v hv w hw hc;exact hRs i w hw v hv ((permutationClose_symm π b _ _).mp hc)
    · exact fun i j hij=>(hTT i j hij).2.2
  have hXroot:∀ v∈X\R₀.rowSet,∀ z∈Z,¬PermutationClose π b v z:=by
    intro v hv z hz
    obtain ⟨hv,hvOld⟩:=Finset.mem_sdiff.mp hv
    rcases Finset.mem_union.mp hv with hv|hv
    · rcases Finset.mem_union.mp hv with hv|hv
      · obtain ⟨av,_,rfl⟩:=Finset.mem_image.mp hv
        exact hLeftSep av hvOld z hz
      · obtain ⟨av,_,rfl⟩:=Finset.mem_image.mp hv
        exact (hRrow av).2.2 z (Finset.mem_union_left _ hz)
    · obtain ⟨i,_,hv⟩:=Finset.mem_biUnion.mp hv
      obtain ⟨av,_,rfl⟩:=Finset.mem_image.mp hv
      exact ((hT i).2.2.2.1 av).2.2 z (Finset.mem_union_left _ (Finset.mem_union_left _ hz))
  have hsize:=marked_diagram_model_size G l n e hn he
  have hTc (i:Fin 3):(T i).rowSet.card≤markedDiagramSize l n e:=
    (T i).rowSet_card.trans (by simpa only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin] using hsize.1 i)
  have hTh (i:Fin 3):(T i).hubSet.card≤markedDiagramSize l n e:=
    (T i).hubSet_card.trans (by simpa only [Fintype.card_sum] using hsize.2 i)
  have hLc:L.rowSet.card≤markedDiagramSize l n e:=L.rowSet_card.trans (by
    have h:=hsize.1 0
    dsimp [markedDiagramOldRows,markedDiagramOldRows_fintype,Fin.cases,Fin.induction,Fin.induction.go] at h
    simpa only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin] using h)
  have hLh:L.hubSet.card≤markedDiagramSize l n e:=L.hubSet_card.trans (by
    have h:=hsize.2 0
    dsimp [markedDiagramOldHubs,markedDiagramOldHubs_fintype,Fin.cases,Fin.induction,Fin.induction.go] at h
    simpa only [Fintype.card_sum] using h)
  have hRc:R.rowSet.card≤markedDiagramSize l n e:=R.rowSet_card.trans (by
    have h:=hsize.1 2
    dsimp [markedDiagramOldRows,markedDiagramOldRows_fintype,Fin.cases,Fin.induction,Fin.induction.go] at h
    simpa only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin] using h)
  have hRh:R.hubSet.card≤markedDiagramSize l n e:=R.hubSet_card.trans (by
    have h:=hsize.2 2
    dsimp [markedDiagramOldHubs,markedDiagramOldHubs_fintype,Fin.cases,Fin.induction,Fin.induction.go] at h
    simpa only [Fintype.card_sum] using h)
  have hRavoid:Disjoint R.rowSet (W∪Z):=by
    apply Finset.disjoint_left.mpr
    intro v hv hz
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hv
    rcases Finset.mem_union.mp hz with hz|hz
    · exact (hRrow a).1 hz
    · exact (hRrow a).2.1 (Finset.mem_union_left _ hz)
  have hTavoid (i:Fin 3):Disjoint (T i).rowSet (W∪Z):=by
    apply Finset.disjoint_left.mpr
    intro v hv hz
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hv
    rcases Finset.mem_union.mp hz with hz|hz
    · exact ((hT i).2.2.2.1 a).1 hz
    · exact ((hT i).2.2.2.1 a).2.1 (Finset.mem_union_left _ (Finset.mem_union_left _ hz))
  have hLX:∀ v∈L.rowSet,v∈W∪Z→v∈R₀.rowSet:=by
    intro v hv hz;obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hv;exact hLold a hz
  have hLZ:Disjoint (L.rowSet\Z) (W∪Z):=by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    have hvR:=hLX v (Finset.mem_sdiff.mp hv).1 hw
    obtain ⟨a,_,ha⟩:=Finset.mem_image.mp hvR
    exact (Finset.mem_sdiff.mp hv).2 (ha ▸ hr a)
  have hextraS:∀ a∈extra,MarkedResourceSupported tail head ktail khead π L.rowSet a:=by
    intro a ha
    exact (L.resources_supported a (hpart.symm ▸ Finset.mem_union_right R₀.resources ha)).2
  have hextraA:=marked_transformer_avoids_old_rows hp L.rowSet ∅ Z (W∪Z) B extra hLZ (by simp)
    (by simpa only [Finset.union_empty] using hextraS) hextraOld
  let D:Fin 5→Finset (Finset V⊕(V×U)):=![L.resources,(T 0).resources,(T 1).resources,(T 2).resources,R.resources]
  refine ⟨{
    rows := X
    hubs := Y
    original_rows := hOldRows.trans (ordinaryFiveUnion_left _ _ _)
    original_hubs := hOldHubs.trans (ordinaryFiveUnion_left _ _ _)
    rows_card := ordinaryFiveUnion_card _ _ _ _ hLc hRc hTc
    hubs_card := ordinaryFiveUnion_card _ _ _ _ hLh hRh hTh
    rows_avoid := ?_
    hubs_avoid := ?_
    rows_separated := hXsep
    rows_root_separated := hXroot
    D := D
    disjoint := hgeom.1
    supported := hgeom.2
    avoid := ?_
    extra := extra
    first := hpart
    first_disjoint := hpartdis
    extra_decomp := hextra
    extra_avoid := hextraA
    last_decomp := hRdec
    P := P
    source := hsource
    image := himage
    roots := ?_
    baseHubs := hPB }⟩
  · intro v hv hz
    rcases Finset.mem_union.mp hv with hv|hv
    · rcases Finset.mem_union.mp hv with hv|hv
      · exact hLX v hv hz
      · exact (Finset.disjoint_left.mp hRavoid hv hz).elim
    · obtain ⟨i,_,hv⟩:=Finset.mem_biUnion.mp hv
      exact (Finset.disjoint_left.mp (hTavoid i) hv hz).elim
  · intro u hu huB
    rcases Finset.mem_union.mp hu with hu|hu
    · rcases Finset.mem_union.mp hu with hu|hu
      · obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hu;exact hLhub a huB
      · obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hu
        exact (hRhub a (Finset.mem_union_left _ huB)).elim
    · obtain ⟨i,_,hu⟩:=Finset.mem_biUnion.mp hu
      obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hu
      exact ((hT i).2.2.1 a (Finset.mem_union_left _ (Finset.mem_union_left _ huB))).elim
  · intro i hi
    have hRa:=fun a ha=>marked_supported_avoids_old hp B hRavoid a (R.resources_supported a ha).2
    have hTa:=fun j a ha=>marked_supported_avoids_old hp B (hTavoid j) a ((T j).resources_supported a ha).2
    fin_cases i
    · exact (hi rfl).elim
    · exact hTa 0
    · exact hTa 1
    · exact hTa 2
    · exact hRa
  · intro j
    rw [hProots,hProots']
    fin_cases j <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three]
    · exact Finset.union_subset (ordinaryFiveUnion_mid L.rowSet R.rowSet (fun i=>(T i).rowSet) 0) (ordinaryFiveUnion_left _ _ _)
    · exact Finset.union_subset (ordinaryFiveUnion_mid L.rowSet R.rowSet (fun i=>(T i).rowSet) 0) (ordinaryFiveUnion_mid L.rowSet R.rowSet (fun i=>(T i).rowSet) 1)
    · exact Finset.union_subset (ordinaryFiveUnion_mid L.rowSet R.rowSet (fun i=>(T i).rowSet) 2) (ordinaryFiveUnion_mid L.rowSet R.rowSet (fun i=>(T i).rowSet) 1)
    · exact Finset.union_subset (ordinaryFiveUnion_mid L.rowSet R.rowSet (fun i=>(T i).rowSet) 2) (ordinaryFiveUnion_right _ _ _)

end Oberwolfach
