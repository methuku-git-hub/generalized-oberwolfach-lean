module

public import Oberwolfach.MarkedDiagramEndpoints
public import Oberwolfach.MarkedUniformTransformerFamily
public import Oberwolfach.MarkedUnionRowSeparation

@[expose] public section

/-! Construct all four transformers in a common marked host and assemble
the two exact absorber decompositions, preserving the global separation,
size and forbidden-resource conclusions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 60000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_diagram_absorber (l:ℕ) (hl:2≤l)
    (ρ σ q₀ β blo bhi:ℝ) (hρ:0<ρ) (hσ:0<σ) (hq₀:0<q₀) (hβ:0<β) (hblo:0<blo) (hbhi:0<bhi):
    ∃ ε:ℝ,0<ε∧∀ M e:ℕ,∃ a₀ b₀:ℕ,∀ f b:ℕ,∀ dF:ℝ,0≤dF→∃ N:ℕ,
    ∀ (V U E K A S:Type) [Fintype V] [Fintype U] [Fintype A] [Fintype S]
      [DecidableEq V] [DecidableEq U] [DecidableEq A] [DecidableEq S],
    N≤Fintype.card V→
    ∀ (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (π:Equiv.Perm V),1≤b→
    ∀ (original:Finset (Finset V⊕(V×U))) (W Z O:Finset V) (B O':Finset U),
    Z.card≤M→O⊆Z→Fintype.card A+Fintype.card S≤e→
    MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l (ρ*Fintype.card V) (σ*Fintype.card V)→
    Function.Injective (markedPhysicalEdge tail head ktail khead π)→
    (B.card:ℝ)≤ε*Fintype.card V+f→(W.card:ℝ)≤ε*Fintype.card V+f→
    ∀ F:SimpleGraph V,permutationConflictGraph π b≤F→
    (∀ v z,HK v z→¬H₀ v z)→(∀ v,(F.degree v:ℝ)≤dF)→
    MarkedCommonPairCycleProfiles tail head ktail khead H₀ HK π b l q₀ β blo bhi ε→
    MarkedHostDiagram (l+4) M tail head ktail khead H₀ HK π b original W Z B O O' A S→
    ∃ C:MarkedSupportedEdgeSet tail head ktail khead π U,
      IsResourceAbsorber (fun D:MarkedWheel tail head ktail khead (l+4) π b H₀ HK=>markedWheelPhysicalResources D)
        original C.edges∧C.rows.card≤a₀∧C.hubs.card≤b₀∧
      (∀ v∈C.rows,v∈W∪Z→v∈O)∧(∀ u∈C.hubs,u∈B→u∈O')∧
      (∀ e∈C.edges,¬MarkedOldResource tail head ktail khead π (W∪Z) B e)∧
      (∀ v∈C.rows\O,∀ w∈C.rows\O,v≠w→¬PermutationClose π b v w)∧
      ∀ v∈C.rows\O,∀ w∈O,¬PermutationClose π b v w:=by
  obtain ⟨ε,hε,hfamily⟩:=marked_uniform_transformer_family l hl ρ σ q₀ β blo bhi hρ hσ hq₀ hβ hblo hbhi
  refine ⟨ε,hε,?_⟩
  intro M e
  obtain ⟨a,b₀,hfamily⟩:=hfamily (5*M) e 4
  refine ⟨5*M+4*a,5*M+4*b₀,?_⟩
  intro f b dF hdF
  obtain ⟨N,hfamily⟩:=hfamily (f+6*M) b dF hdF
  refine ⟨N,?_⟩
  intro V U E K A S _ _ _ _ _ _ _ _ hn tail head ktail khead H₀ HK π hb original W Z O B O' hZ hOZ he Q hp hB hW F hconf htypes hF Profiles D
  let W':=W∪Z∪D.rows
  let B':=B∪D.hubs
  have hW':(W'.card:ℝ)≤ε*Fintype.card V+(f+6*M:ℕ):=by
    have hc:W'.card≤W.card+6*M:=by
      have h₁:=Finset.card_union_le W Z
      have h₂:=Finset.card_union_le (W∪Z) D.rows
      have h₃:=D.rows_card
      dsimp [W'];omega
    have hc':(W'.card:ℝ)≤W.card+6*M:=by exact_mod_cast hc
    push_cast;linarith only [hc',hW]
  have hB':(B'.card:ℝ)≤ε*Fintype.card V+(f+6*M:ℕ):=by
    have hc:B'.card≤B.card+6*M:=by
      have h₁:=Finset.card_union_le B D.hubs
      have h₂:=D.hubs_card
      dsimp [B'];omega
    have hc':(B'.card:ℝ)≤B.card+6*M:=by exact_mod_cast hc
    push_cast;linarith only [hc',hB]
  obtain ⟨C,hC,hCC,hsepC⟩:=hfamily V U E K A S hn tail head ktail khead H₀ HK π hb D.P W' D.rows B'
    D.rows_card D.roots D.baseHubs he Q hp hB' hW' F hconf htypes hF Profiles
  let K':=fun i=>(C i).edges
  let allD:=Finset.univ.biUnion D.D
  have hKall (i:Fin 4):Disjoint (K' i) allD:=by
    apply Finset.disjoint_left.mpr
    intro e he hde
    obtain ⟨j,_,hde⟩:=Finset.mem_biUnion.mp hde
    exact (hC i).2.2.2.2.2.1 e he (marked_old_resource_mono Finset.subset_union_right Finset.subset_union_right e (D.supported j e hde))
  have hDall:∀ i,i≤4→finiteFiveAt D.D i⊆allD:=by
    intro i hi
    rw [show finiteFiveAt D.D i=D.D ⟨i,by omega⟩ from finiteFiveAt_apply D.D ⟨i,by omega⟩]
    exact Finset.subset_biUnion_of_mem D.D (Finset.mem_univ _)
  have habs:IsResourceAbsorber (fun D':MarkedWheel tail head ktail khead (l+4) π b H₀ HK=>markedWheelPhysicalResources D')
      original (markedDiagramAbsorberEdges D K'):=by
    have hfirst:finiteFiveAt D.D 0=original∪D.extra:=by simpa [finiteFiveAt] using D.first
    have hlast:HasResourceDecomposition (fun D':MarkedWheel tail head ktail khead (l+4) π b H₀ HK=>markedWheelPhysicalResources D') (finiteFiveAt D.D 4):=by
      simpa [finiteFiveAt] using D.last_decomp
    simpa [markedDiagramAbsorberEdges,finiteFiveAt] using
      finite_four_transformer_absorber _ (finiteFiveAt D.D) (fun i=>(D.P i).source) (fun i=>(D.P i).image)
        K' original D.extra allD hfirst D.first_disjoint D.extra_decomp hlast
        (fun i=>(hC i).2.2.1) D.chain_endpoints D.chain_disjoint hCC hKall hDall
  let X:=D.rows∪Finset.univ.biUnion (fun i=>(C i).rows)
  let H:=D.hubs∪Finset.univ.biUnion (fun i=>(C i).hubs)
  have hsupport:∀ e∈markedDiagramAbsorberEdges D K',MarkedOldResource tail head ktail khead π X H e:=by
    intro e he
    rcases markedDiagramAbsorberEdges_membership D K' e he with he|⟨i,he⟩|⟨i,_,he⟩
    · have he':e∈D.D 0:=by rw [D.first];exact Finset.mem_union_right _ he
      exact marked_old_resource_mono Finset.subset_union_left Finset.subset_union_left e (D.supported 0 e he')
    · exact marked_old_resource_mono
        ((Finset.subset_biUnion_of_mem (fun j=>(C j).rows) (Finset.mem_univ i)).trans Finset.subset_union_right)
        ((Finset.subset_biUnion_of_mem (fun j=>(C j).hubs) (Finset.mem_univ i)).trans Finset.subset_union_right) e ((C i).supported e he)
    · exact marked_old_resource_mono Finset.subset_union_left Finset.subset_union_left e (D.supported i e he)
  have hXc:X.card≤5*M+4*a:=by
    have hc:(Finset.univ.biUnion (fun i=>(C i).rows)).card≤4*a:=by
      calc
        _≤∑ i:Fin 4,(C i).rows.card:=Finset.card_biUnion_le
        _≤∑ _i:Fin 4,a:=Finset.sum_le_sum (fun i _=>(hC i).1)
        _=4*a:=by simp
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add D.rows_card hc)
  have hHc:H.card≤5*M+4*b₀:=by
    have hc:(Finset.univ.biUnion (fun i=>(C i).hubs)).card≤4*b₀:=by
      calc
        _≤∑ i:Fin 4,(C i).hubs.card:=Finset.card_biUnion_le
        _≤∑ _i:Fin 4,b₀:=Finset.sum_le_sum (fun i _=>(hC i).2.1)
        _=4*b₀:=by simp
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add D.hubs_card hc)
  have hsep:=marked_union_row_separation π b D.rows O (fun i=>(C i).rows) D.original_rows
    D.rows_separated (fun v hv w hw=>D.rows_root_separated v hv w (hOZ hw))
    (fun i=>(hC i).2.2.2.2.2.2.1) (fun i=>(hC i).2.2.2.2.2.2.2) hsepC
  let out:MarkedSupportedEdgeSet tail head ktail khead π U:={
    rows := X
    hubs := H
    edges := markedDiagramAbsorberEdges D K'
    supported := hsupport }
  refine ⟨out,habs,hXc,hHc,?_,?_,?_,hsep.1,hsep.2⟩
  · intro v hv hvW
    rcases Finset.mem_union.mp hv with hv|hv
    · exact D.rows_avoid v hv hvW
    · obtain ⟨i,_,hv⟩:=Finset.mem_biUnion.mp hv
      have hvD: v∈D.rows:=(hC i).2.2.2.1 v hv (Finset.mem_union_left _ hvW)
      exact D.rows_avoid v hvD hvW
  · intro u hu huB
    rcases Finset.mem_union.mp hu with hu|hu
    · exact D.hubs_avoid u hu huB
    · obtain ⟨i,_,hu⟩:=Finset.mem_biUnion.mp hu
      obtain ⟨s,hs|hs⟩:=(hC i).2.2.2.2.1 u hu (Finset.mem_union_left _ huB)
      · exact D.hubs_avoid u (hs ▸ (D.active_hubs i s).1) huB
      · exact D.hubs_avoid u (hs ▸ (D.active_hubs i s).2) huB
  · intro e he
    rcases markedDiagramAbsorberEdges_membership D K' e he with he|⟨i,he⟩|⟨i,hi,he⟩
    · exact D.extra_avoid e he
    · intro hold
      exact (hC i).2.2.2.2.2.1 e he (marked_old_resource_mono
        (Finset.subset_union_left.trans Finset.subset_union_left) Finset.subset_union_left e hold)
    · exact D.avoid i hi e he

end Oberwolfach
