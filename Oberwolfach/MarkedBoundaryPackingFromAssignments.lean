module

public import Oberwolfach.MarkedAssignedBoundaryPacking
public import Oberwolfach.MarkedEndpointAssignmentData
public import Oberwolfach.MarkedBoundaryArcIndices
public import Oberwolfach.MarkedInnerResources

@[expose] public section

/-! All boundary paths are constructed from the selected typed endpoint
bijections. Their global incidence bounds are derived from the physical
union degree; their root arcs are the original distinct boundary arcs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open MarkedEndpointPairing
variable {V U E T J:Type} [Fintype V] [Fintype U] [Fintype J]
    [DecidableEq V] [DecidableEq U] [DecidableEq J]
    {tail head:E→V} {ktail khead:T→V} {H₀ HK:V→U→Prop}
    {π:Equiv.Perm V} {b l:ℕ} {c:ℝ}

theorem marked_boundary_packing_from_assignments
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
    (G:SimpleGraph V) (hGX:GraphSupportedOn X G) (δ:ℝ) (hδ:0≤δ) (hG:∀ v,(G.degree v:ℝ)≤δ)
    (hbudget:(Fintype.card (Σ j,Y₀ j⊕Y₁ j)*(l+4):ℕ)/(K:ℝ)+D+(D*(l+4):ℕ)+
      (l+5)*(2*b+1)+2*(δ+4*(K+D:ℕ))<c):
    ∃ C:Fin (Fintype.card (Σ j,Y₀ j⊕Y₁ j))→MarkedWheel tail head ktail khead (l+3) π b H₀ HK,
      (∀ i j,i≠j→Disjoint (markedWheelPhysicalResources (C i)) (markedWheelPhysicalResources (C j)))∧
      (∀ j a,∃ i,Sum.inl (markedPhysicalEdge tail head ktail khead π (incoming j a))∈markedWheelPhysicalResources (C i))∧
      (∀ j a,∃ i,Sum.inl (markedPhysicalEdge tail head ktail khead π (outgoing j a))∈markedWheelPhysicalResources (C i))∧
      (∀ j u,u∈Y₀ j∪Y₁ j→∃ i,Sum.inr (root j,u)∈markedWheelPhysicalResources (C i))∧
      (∀ i,Disjoint (markedWheelRimGraph (C i)) G)∧
      (∀ v,(spanningRestriction (markedFamilyRim C) X).degree v≤4*(K+D))∧
      (∀ v∈X,(Finset.univ.filter (markedFamilySpokes C v)).card≤K+D)∧
      (∀ u,(Finset.univ.filter (fun v=>markedFamilySpokes C v u)).card≤D*(l+4))∧
      (∀ i,∃ j,(C i).2.val∈Y₀ j∪Y₁ j∧markedWheelRows (C i)⊆insert (root j) X)∧
      (∀ i e,e∈markedCyclePhysicalEdges tail head ktail khead (l+3) π b (C i).1→
        e⊆X∨(∃ j a,e=markedPhysicalEdge tail head ktail khead π (incoming j a))∨
          ∃ j a,e=markedPhysicalEdge tail head ktail khead π (outgoing j a)) := by
  let I:=Σ j,Y₀ j⊕Y₁ j
  let N:=Fintype.card I
  let e:Fin N≃I:=(Fintype.equivFin I).symm
  let v:=fun i:Fin N=>root (e i).1
  let a:=assignedOutgoing P∘e
  let z:=assignedIncoming P∘e
  let u:=assignedHub P∘e
  let ji:=assignedIncomingType P∘e
  let jo:=assignedOutgoingType P∘e
  let inc:I→E⊕T:=fun i=>incoming i.1 ((P i.1).incoming.symm i.2)
  let out:I→E⊕T:=fun i=>outgoing i.1 ((P i.1).outgoing.symm i.2)
  have hiinj:Function.Injective inc:=dependent_assigned_edges_injective root incoming
    (fun j=>(P j).incoming.symm) (Sum.elim head khead) hinhead
  have hoinj:Function.Injective out:=dependent_assigned_edges_injective root outgoing
    (fun j=>(P j).outgoing.symm) (Sum.elim tail ktail) houttail
  have hihead (i:Fin N):Sum.elim head khead (inc (e i))=v i:=hinhead _ _
  have hitail (i:Fin N):Sum.elim tail ktail (inc (e i))=z i:=hintail _ _
  have hotail (i:Fin N):Sum.elim tail ktail (out (e i))=v i:=houttail _ _
  have hohead (i:Fin N):Sum.elim head khead (out (e i))=a i:=houthead _ _
  have hitype (i:Fin N):(inc (e i)).isRight=ji i:=hintype _ _
  have hotype (i:Fin N):(out (e i)).isRight=jo i:=houttype _ _
  have ha (i:Fin N):a i∈X:=hXX _ (assigned_label_membership P (e i)).2
  have hz (i:Fin N):z i∈X:=hAX _ (assigned_label_membership P (e i)).1
  have hrims:=marked_assigned_boundary_root_rims_disjoint tail head ktail khead π hphys X v
    (inc∘e) (out∘e) (hiinj.comp e.injective) (hoinj.comp e.injective) hihead hotail
    (fun i=>hrootX _) (fun i=>by simpa only [Function.comp_apply,hitail] using hz i)
  have hrootspokes:Function.Injective (fun i:Fin N=>(v i,u i)):=
    (assigned_root_spokes_injective P root).comp e.injective
  have hend (x:V):(Finset.univ.filter (fun i:Fin N=>x=a i∨x=z i)).card≤D:=by
    have he:=(filter_card_reindex_equiv e (fun i=>x=assignedOutgoing P i∨x=assignedIncoming P i))
    calc
      _ = _ := by convert he using 1 <;> congr!
      _ ≤ D := (assigned_endpoint_occurrences P hcross x).trans (hdeg _)
  have hhub (w:U):(Finset.univ.filter (fun i:Fin N=>u i=w)).card≤D:=by
    have he:=filter_card_reindex_equiv e (fun i=>assignedHub P i=w)
    calc
      _ = _ := by convert he using 1 <;> congr!
      _ ≤ D := (assigned_hub_occurrences P hcross w).trans (hdeg _)
  let R:=fun x w=>(⨆ j,(P j).graph).Adj (Sum.inl x) (Sum.inr w)
  have hRa (i:Fin N):R (a i) (u i):=SimpleGraph.iSup_adj.mpr ⟨(e i).1,(assigned_endpoint_edges P (e i)).1⟩
  have hRz (i:Fin N):R (z i) (u i):=SimpleGraph.iSup_adj.mpr ⟨(e i).1,(assigned_endpoint_edges P (e i)).2⟩
  have hR (w:U):(Finset.univ.filter (fun x=>R x w)).card≤D:=
    (physical_spoke_deleted_col (⨆ j,(P j).graph) w).trans (hdeg _)
  have htypes (i:Fin N):¬(ji i=true∧jo i=true):=assigned_types_compatible P (e i)
  have hroot (i:Fin N):if ji i then HK (v i) (u i) else H₀ (v i) (u i):=by
    have hsp (idx:I):if idx.2.isRight then HK (root idx.1) (assignedHub P idx) else H₀ (root idx.1) (assignedHub P idx):=by
      rcases idx with ⟨j,y⟩
      cases y with
      | inl y=>exact hY₀ j y.val y.property
      | inr y=>exact hY₁ j y.val y.property
    have hh:=assigned_incoming_type P (e i)
    change (if assignedIncomingType P (e i) then HK (v i) (u i) else H₀ (v i) (u i))
    rw [hh]
    exact hsp (e i)
  obtain ⟨C,hC,hdis,hcap,hRim,hRow,hCol⟩:=marked_assigned_boundary_packing X Q hl hb hX N K D D D hK
    v a z u ji jo (fun i=>hrootX _) ha hz htypes (fun i=>assigned_separated P (e i))
    (fun i=>hsepX _ _ (assigned_label_membership P (e i)).2)
    (fun i=>hsepA _ _ (assigned_label_membership P (e i)).1)
    (fun i=>(assigned_spokes P (e i)).2) (fun i=>(assigned_spokes P (e i)).1) hroot
    (by intro i;simpa only [hotype,hotail,hohead] using markedArcPresent_of_edge tail head ktail khead (out (e i)))
    (by intro i;simpa only [hitype,hitail,hihead] using markedArcPresent_of_edge tail head ktail khead (inc (e i)))
    (by simpa only [Function.comp_apply,hohead,hitail,hitype,hotype] using hrims)
    hrootspokes hend hhub R hRa hRz hR
    (fun i j hij hu=>assigned_same_hub_endpoints_disjoint P hcross (e i) (e j)
      (fun he=>hij (e.injective he)) hu) G hGX δ hδ hG hbudget
  have hcov (i:Fin N):
      Sum.inl (markedPhysicalEdge tail head ktail khead π (inc (e i)))∈markedWheelPhysicalResources (C i)∧
      Sum.inl (markedPhysicalEdge tail head ktail khead π (out (e i)))∈markedWheelPhysicalResources (C i)∧
      Sum.inr (v i,u i)∈markedWheelPhysicalResources (C i):=by
    obtain ⟨hCu,p,hp0,hplast,hcoord,_,_,_⟩:=hC i
    have hh:=marked_assigned_row_root_resources (by omega:2≤l+2) p (v i) (ji i) (jo i) (htypes i) (C i) hcoord
    rw [hp0,hplast,hCu] at hh
    have hi:markedPhysicalEdge tail head ktail khead π (inc (e i))=if ji i then {z i,π (v i)} else {z i,v i}:=by
      rw [markedPhysicalEdge_typed_formula,hihead,hitail,hitype]
    have ho:markedPhysicalEdge tail head ktail khead π (out (e i))=if jo i then {v i,π (a i)} else {v i,a i}:=by
      rw [markedPhysicalEdge_typed_formula,hotail,hohead,hotype]
    rw [hi,ho]
    exact ⟨hh.2.1,hh.1,hh.2.2⟩
  have hcovHub (idx:I):Sum.inr (root idx.1,assignedHub P idx)∈markedWheelPhysicalResources (C (e.symm idx)):=by
    have hh:=(hcov (e.symm idx)).2.2
    change Sum.inr (root (e (e.symm idx)).1,assignedHub P (e (e.symm idx)))∈_ at hh
    simpa only [e.apply_symm_apply] using hh
  have hhubmem (idx:I):assignedHub P idx∈Y₀ idx.1∪Y₁ idx.1:=by
    rcases idx with ⟨j,y⟩
    cases y with
    | inl y=>exact Finset.mem_union_left _ y.property
    | inr y=>exact Finset.mem_union_right _ y.property
  refine ⟨C,hdis,?_,?_,?_,?_,hRim,hRow,hCol,?_,?_⟩
  · intro j w
    let idx:I:=⟨j,(P j).incoming w⟩
    refine ⟨e.symm idx,?_⟩
    have hh:=(hcov (e.symm idx)).1
    simpa only [e.apply_symm_apply,inc,idx,(P j).incoming.symm_apply_apply] using hh
  · intro j w
    let idx:I:=⟨j,(P j).outgoing w⟩
    refine ⟨e.symm idx,?_⟩
    have hh:=(hcov (e.symm idx)).2.1
    simpa only [e.apply_symm_apply,out,idx,(P j).outgoing.symm_apply_apply] using hh
  · intro j w hw
    rcases Finset.mem_union.mp hw with hw|hw
    · exact ⟨e.symm ⟨j,Sum.inl ⟨w,hw⟩⟩,hcovHub ⟨j,Sum.inl ⟨w,hw⟩⟩⟩
    · exact ⟨e.symm ⟨j,Sum.inr ⟨w,hw⟩⟩,hcovHub ⟨j,Sum.inr ⟨w,hw⟩⟩⟩
  · intro i;obtain ⟨_,p,_,_,_,_,_,hG⟩:=hC i;exact hG
  · intro i
    obtain ⟨hCu,p,hp0,hplast,hcoord,hpX,_,_⟩:=hC i
    refine ⟨(e i).1,?_,?_⟩
    · rw [hCu]
      exact hhubmem (e i)
    · rw [marked_one_root_rows p (v i) _ (C i) hcoord]
      intro x hx
      rcases Finset.mem_insert.mp hx with he|he
      · exact he ▸ Finset.mem_insert_self _ _
      · obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp he
        exact Finset.mem_insert_of_mem (hpX j)

  · intro i edge hedge
    obtain ⟨_,p,hp0,hplast,hcoord,hpX,_,_⟩:=hC i
    have hc:=marked_assigned_row_rim_classification (by omega:2≤l+2) p (v i) (ji i) (jo i)
      (htypes i) X (fun x hx=>(hX x).mpr hx) hpX (C i) hcoord edge hedge
    rcases hc with hc|hc
    · exact Or.inl hc
    · rw [markedRowRootRims,hp0,hplast] at hc
      rcases Finset.mem_insert.mp hc with hc|hc
      · refine Or.inr (Or.inr ⟨(e i).1,(P (e i).1).outgoing.symm (e i).2,?_⟩)
        have he:markedPhysicalEdge tail head ktail khead π (out (e i))=
            if jo i then {v i,π (a i)} else {v i,a i}:=by
          rw [markedPhysicalEdge_typed_formula,hotail,hohead,hotype]
        exact hc.trans he.symm
      · refine Or.inr (Or.inl ⟨(e i).1,(P (e i).1).incoming.symm (e i).2,?_⟩)
        have he:markedPhysicalEdge tail head ktail khead π (inc (e i))=
            if ji i then {z i,π (v i)} else {z i,v i}:=by
          rw [markedPhysicalEdge_typed_formula,hihead,hitail,hitype]
        exact (Finset.mem_singleton.mp hc).trans he.symm

end Oberwolfach
