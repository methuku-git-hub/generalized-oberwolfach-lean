module

public import Oberwolfach.MarkedInitialDiagramData
public import Oberwolfach.MarkedPackedAttachmentIdentity
public import Oberwolfach.MarkedInitialFamilyOldSpokes

@[expose] public section

/-! The constructed diagram supplies the two exact decompositions and the
signed resource identity used by the hub switches. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K A S:Type} [Fintype V] [Fintype U] [Fintype A] [Fintype S]
    [DecidableEq V] [DecidableEq U] [DecidableEq A] [DecidableEq S]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ}
    {src dst:A→V} {row:S→V} {φ:V→V} {u u':S→U} {jr:A→Bool} {js:S→Bool}
    {W Z:Finset V} {B:Finset U}

def markedRootGraphResources (π:Equiv.Perm V) (src dst:A→V) (row:S→V) (jr:A→Bool) (u:S→U):
    Finset (Finset V⊕(V×U)):=
  Finset.univ.image (fun e=>Sum.inl (if jr e then ({src e,π (dst e)}:Finset V) else {src e,dst e}))∪
    Finset.univ.image (fun s=>Sum.inr (row s,u s))

def markedDiagramPlus (D:MarkedInitialDiagram tail head ktail khead H₀ HK π b l src dst row φ u u' jr js W Z B):
    Finset (Finset V⊕(V×U)):=
  Finset.univ.biUnion (fun i:A⊕(S⊕(Σ v,DirectedIncidence src dst v))=>
    markedWheelPhysicalResources (Sum.elim D.RC (Sum.elim D.SC D.VD) i))

def markedDiagramMinus (D:MarkedInitialDiagram tail head ktail khead H₀ HK π b l src dst row φ u u' jr js W Z B):
    Finset (Finset V⊕(V×U)):=
  Finset.univ.biUnion (fun i:A⊕(S⊕(Σ v,DirectedIncidence src dst v))=>
    markedWheelPhysicalResources (Sum.elim D.RD (Sum.elim D.SD D.VC) i))

theorem marked_diagram_exact_identity (hl:0≤l)
    (D:MarkedInitialDiagram tail head ktail khead H₀ HK π b l src dst row φ u u' jr js W Z B)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π)) (ψ:U→U) (hu':∀ s,u' s=ψ (u s))
    (hr:Function.Injective (fun e=>if jr e then ({src e,π (dst e)}:Finset V) else {src e,dst e}))
    (hr':Function.Injective (fun e=>if jr e then ({φ (src e),π (φ (dst e))}:Finset V) else {φ (src e),φ (dst e)}))
    (hs:Function.Injective (fun s=>(row s,u s))) (hs':Function.Injective (fun s=>(φ (row s),u' s))):
    HasResourceDecomposition (markedWheelPhysicalResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
      (m:=l+4) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=HK)) (markedDiagramPlus D)∧
    HasResourceDecomposition (markedWheelPhysicalResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
      (m:=l+4) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=HK)) (markedDiagramMinus D)∧
    ∀ e:Finset V⊕(V×U),(if e∈markedDiagramPlus D then (1:ℤ) else 0)-(if e∈markedDiagramMinus D then 1 else 0)=
      (if e∈markedRootGraphResources π src dst row jr u then 1 else 0)-
      (if e∈markedRootGraphResources π (fun a=>φ (src a)) (fun a=>φ (dst a)) (fun s=>φ (row s)) jr u' then 1 else 0)+
      ∑ z:U,((if e∈(spokePathHubVertices (l+4) D.ps u z).image (fun v=>Sum.inr (v,z)) then 1 else 0)-
        (if e∈(spokePathHubVertices (l+4) D.ps u z).image (fun v=>Sum.inr (v,ψ z)) then 1 else 0)):=by
  exact marked_packed_attachment_identity (l+2) (by omega) hp src dst row φ D.hub u u' jr js D.a D.d D.τ
    (fun e=>D.pr e) D.ps (fun z=>D.pv z) (fun z=>markedIncidenceSpokeType jr (D.τ z.1 z.2))
    D.RC D.RD D.SC D.SD D.VC D.VD D.rimCoordinates D.imageRimCoordinates D.rimHubs
    D.spokeCoordinates D.imageSpokeCoordinates D.spokeHubs D.vertexCoordinates D.imageVertexCoordinates D.vertexHubs
    (fun v e=>⟨(D.incomingType v e).symm,(D.vertexEnds ⟨v,Sum.inl e⟩).1,(D.vertexEnds ⟨v,Sum.inl e⟩).2⟩)
    (fun v e=>⟨D.outgoingType v e,(D.vertexEnds ⟨v,Sum.inr e⟩).1,(D.vertexEnds ⟨v,Sum.inr e⟩).2⟩)
    ψ hu' D.spokeDisjoint hr hr' hs hs' D.plusPacking D.minusPacking

theorem marked_diagram_opposite_spokes
    (D:MarkedInitialDiagram tail head ktail khead H₀ HK π b l src dst row φ u u' jr js W Z B)
    (ψ:U→U) (hu':∀ s,u' s=ψ (u s)) (hU:∀ s,u s∈B∧u' s∈B)
    (hψ:∀ s,u s≠u' s) (hR:∀ s,row s∈Z∧φ (row s)∈Z):
    ∀ z v,v∈spokePathHubVertices (l+4) D.ps u z→
      (Sum.inr (v,ψ z):Finset V⊕(V×U))∉markedDiagramPlus D∧
      (Sum.inr (v,z):Finset V⊕(V×U))∉markedDiagramMinus D:=by
  apply marked_initial_family_old_spokes D.ps row (fun s=>φ (row s)) u ψ js B
    (fun s=>by simpa only [←hu'] using hU s) (fun s=>by simpa only [←hu'] using hψ s)
    D.RC D.RD D.SC D.SD D.VC D.VD
  · intro e
    simpa only [(D.rimHubs e).1,(D.rimHubs e).2] using And.intro (D.freshHub e) (D.freshHub e)
  · intro z
    simpa only [(D.vertexHubs z).1,(D.vertexHubs z).2] using
      And.intro (D.freshHub (directedIncidenceEdge (D.τ z.1 z.2))) (D.freshHub (directedIncidenceEdge (D.τ z.1 z.2)))
  · exact D.spokeCoordinates
  · exact D.imageSpokeCoordinates
  · intro s
    exact ⟨(D.spokeHubs s).1,(D.spokeHubs s).2.trans (hu' s)⟩
  · intro s t k
    exact ⟨fun he=>(D.spokeAvoid s k).2.1 (he ▸ (hR t).1),fun he=>(D.spokeAvoid s k).2.1 (he ▸ (hR t).2)⟩
  · exact D.spokeDisjoint

end Oberwolfach
