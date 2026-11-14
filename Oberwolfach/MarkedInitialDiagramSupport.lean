module

public import Oberwolfach.MarkedInitialDiagramIdentity
public import Oberwolfach.MarkedResourceSupport

@[expose] public section

/-! The actual initial diagram has bounded auxiliary row support. Marked
physical heads are handled through the fixed representation map. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K A S:Type} [Fintype V] [Fintype U] [Fintype A] [Fintype S]
    [DecidableEq V] [DecidableEq U] [DecidableEq A] [DecidableEq S]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ}
    {src dst:A→V} {row:S→V} {φ:V→V} {u u':S→U} {jr:A→Bool} {js:S→Bool}
    {W Z:Finset V} {B:Finset U}

def markedDiagramRows (D:MarkedInitialDiagram tail head ktail khead H₀ HK π b l src dst row φ u u' jr js W Z B):Finset V:=
  Z∪markedPathUnion (l+3) (l+4) (fun e=>D.pr e) (fun s=>D.ps s)∪
    Finset.univ.biUnion (fun z=>Finset.univ.image (D.pv z))

theorem marked_diagram_rows_card
    (D:MarkedInitialDiagram tail head ktail khead H₀ HK π b l src dst row φ u u' jr js W Z B):
    (markedDiagramRows D).card≤Z.card+Fintype.card A*(l+3)+Fintype.card S*(l+4)+2*Fintype.card A*(l+4):=by
  have hv:(Finset.univ.biUnion (fun z=>Finset.univ.image (D.pv z))).card≤2*Fintype.card A*(l+4):=by
    calc
      _≤∑ z:Σ v,DirectedIncidence src dst v,(Finset.univ.image (D.pv z)).card:=Finset.card_biUnion_le
      _≤∑ _:Σ v,DirectedIncidence src dst v,(l+4):=Finset.sum_le_sum (fun z _=>by simpa using Finset.card_image_le (f:=D.pv z) (s:=Finset.univ))
      _=2*Fintype.card A*(l+4):=by simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,directed_incidence_total_card]
  have hp:=markedPathUnion_card (l+3) (l+4) (fun e=>D.pr e) (fun s=>D.ps s)
  have h₁:=Finset.card_union_le Z (markedPathUnion (l+3) (l+4) (fun e=>D.pr e) (fun s=>D.ps s))
  have h₂:=Finset.card_union_le (Z∪markedPathUnion (l+3) (l+4) (fun e=>D.pr e) (fun s=>D.ps s))
    (Finset.univ.biUnion (fun z=>Finset.univ.image (D.pv z)))
  unfold markedDiagramRows
  omega

theorem marked_diagram_rows_root
    (D:MarkedInitialDiagram tail head ktail khead H₀ HK π b l src dst row φ u u' jr js W Z B):Z⊆markedDiagramRows D:=
  fun _ h=>Finset.mem_union_left _ (Finset.mem_union_left _ h)

theorem marked_diagram_rows_path
    (D:MarkedInitialDiagram tail head ktail khead H₀ HK π b l src dst row φ u u' jr js W Z B):
    markedPathUnion (l+3) (l+4) (fun e=>D.pr e) (fun s=>D.ps s)⊆markedDiagramRows D:=
  fun _ h=>Finset.mem_union_left _ (Finset.mem_union_right _ h)

theorem marked_diagram_rows_vertex
    (D:MarkedInitialDiagram tail head ktail khead H₀ HK π b l src dst row φ u u' jr js W Z B)
    (z:Σ v,DirectedIncidence src dst v) (k:Fin (l+4)):D.pv z k∈markedDiagramRows D:=
  Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨z,Finset.mem_univ _,Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩⟩)

theorem marked_diagram_supported
    (D:MarkedInitialDiagram tail head ktail khead H₀ HK π b l src dst row φ u u' jr js W Z B)
    (hr:∀ e,src e∈Z∧dst e∈Z∧φ (src e)∈Z∧φ (dst e)∈Z)
    (hs:∀ s,row s∈Z∧φ (row s)∈Z):
    (∀ e∈markedDiagramPlus D,MarkedResourceSupported tail head ktail khead π (markedDiagramRows D) e)∧
    (∀ e∈markedDiagramMinus D,MarkedResourceSupported tail head ktail khead π (markedDiagramRows D) e):=by
  have one {n:ℕ} (x:V) (p:Fin n→V) (hx:x∈markedDiagramRows D) (hp:∀ k,p k∈markedDiagramRows D):
      ∀ i:Fin (n+1),Fin.cons (α:=fun _=>V) x p i∈markedDiagramRows D:=by
    intro i;refine Fin.cases hx (fun k=>hp k) i
  have rooted {n:ℕ} (o:Equiv.Perm (Fin (n+1))) (x:V) (p:Fin n→V)
      (hx:x∈markedDiagramRows D) (hp:∀ k,p k∈markedDiagramRows D):
      ∀ i,rootedCycleOrder o x p i∈markedDiagramRows D:=by
    intro i;exact one x p hx hp (o i)
  have hroot:∀ z:Σ v,DirectedIncidence src dst v,z.1∈Z∧φ z.1∈Z:=by
    rintro ⟨v,e|e⟩
    · simpa only [e.property] using And.intro (hr e.val).2.1 (hr e.val).2.2.2
    · simpa only [e.property] using And.intro (hr e.val).1 (hr e.val).2.2.1
  have hp:∀ e k,D.pr e k∈markedDiagramRows D:=fun e k=>marked_diagram_rows_path D (markedPathUnion_rim _ _ _ _ e k)
  have hq:∀ s k,D.ps s k∈markedDiagramRows D:=fun s k=>marked_diagram_rows_path D (markedPathUnion_spoke _ _ _ _ s k)
  have hRC:∀ e i,(D.RC e).1.val i∈markedDiagramRows D:=by
    intro e i;rw [D.rimCoordinates]
    exact one _ _ (marked_diagram_rows_root D (hr e).1)
      (one _ _ (marked_diagram_rows_root D (hr e).2.1) (hp e)) _
  have hRD:∀ e i,(D.RD e).1.val i∈markedDiagramRows D:=by
    intro e i;rw [D.imageRimCoordinates]
    exact one _ _ (marked_diagram_rows_root D (hr e).2.2.1)
      (one _ _ (marked_diagram_rows_root D (hr e).2.2.2) (hp e)) _
  have hSC:∀ s i,(D.SC s).1.val i∈markedDiagramRows D:=by
    intro s i;rw [D.spokeCoordinates]
    exact rooted _ _ _ (marked_diagram_rows_root D (hs s).1) (hq s) i
  have hSD:∀ s i,(D.SD s).1.val i∈markedDiagramRows D:=by
    intro s i;rw [D.imageSpokeCoordinates]
    exact rooted _ _ _ (marked_diagram_rows_root D (hs s).2) (hq s) i
  have hVC:∀ z i,(D.VC z).1.val i∈markedDiagramRows D:=by
    intro z i;rw [D.vertexCoordinates]
    exact rooted _ _ _ (marked_diagram_rows_root D (hroot z).1) (marked_diagram_rows_vertex D z) i
  have hVD:∀ z i,(D.VD z).1.val i∈markedDiagramRows D:=by
    intro z i;rw [D.imageVertexCoordinates]
    exact rooted _ _ _ (marked_diagram_rows_root D (hroot z).2) (marked_diagram_rows_vertex D z) i
  have wheel (C:MarkedWheel tail head ktail khead (l+4) π b H₀ HK) (hC:∀ i,C.1.val i∈markedDiagramRows D):
      ∀ e∈markedWheelPhysicalResources C,MarkedResourceSupported tail head ktail khead π (markedDiagramRows D) e:=by
    rw [markedWheelPhysicalResources_eq_atHub]
    exact marked_cycle_at_hub_supported C.1 C.2.val _ hC
  constructor
  · intro e he
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp he
    rcases i with a|(s|z)
    · exact wheel (D.RC a) (hRC a) e hi
    · exact wheel (D.SC s) (hSC s) e hi
    · exact wheel (D.VD z) (hVD z) e hi
  · intro e he
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp he
    rcases i with a|(s|z)
    · exact wheel (D.RD a) (hRD a) e hi
    · exact wheel (D.SD s) (hSD s) e hi
    · exact wheel (D.VC z) (hVC z) e hi

end Oberwolfach
