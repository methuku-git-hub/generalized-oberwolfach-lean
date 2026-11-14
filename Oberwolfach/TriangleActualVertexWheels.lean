module

public import Oberwolfach.TrianglePathEndpointGeometry
public import Oberwolfach.TriangleVertexWheelPair
public import Oberwolfach.TriangleWheelFamilyPacking

@[expose] public section

/-! The triangular vertex-wheel family, including the permitted sharing
of a rim-path vertex by the two ends of an edge. No internal vertices or
new common-neighbour assumption are needed after the edge choices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

 theorem triangular_actual_vertex_wheels (G Q F:SimpleGraph V) (H₀ H:V→U→Prop) (φ:V→V)
    (b:∀ v,G.neighborSet v≃({u:U // H₀ v u}×Fin 2))
    (σ:∀ v,Equiv.Perm (G.neighborSet v)) (hσ:∀ v w,σ v w≠w) (h:G.edgeFinset↪U)
    (p:(G.edgeFinset⊕{e:V×U // H₀ e.1 e.2})→(Σ a:V,Σ c:V,Q.Walk a c))
    (R W:Finset V)
    (hroot:∀ d:Σ v,G.neighborSet v,d.1∈R∧φ d.1∈R∧d.1≠φ d.1)
    (hφ:∀ v w,G.Adj v w→φ v≠φ w)
    (hrim:∀ e:G.edgeFinset,(p (.inl e)).2.2.length=0)
    (hsp:∀ e:{e:V×U // H₀ e.1 e.2},(p (.inr e)).2.2.IsPath∧0<(p (.inr e)).2.2.length)
    (hpW:∀ i,∀ v∈(p i).2.2.support,v∈W∧v∉R)
    (hdis:∀ i j,i≠j→Disjoint (p i).2.2.support.toFinset (p j).2.2.support.toFinset)
    (hFF:∀ i j,∀ v∈(p i).2.2.support,∀ w∈(p j).2.2.support,¬F.Adj v w)
    (hFR:∀ i,∀ v∈(p i).2.2.support,∀ w∈R,¬F.Adj v w)
    (hends:∀ e:G.edgeFinset,Q.Adj e.val.out.1 (p (.inl e)).1 ∧
      Q.Adj (φ e.val.out.1) (p (.inl e)).1 ∧ Q.Adj e.val.out.2 (p (.inl e)).2.1 ∧
      Q.Adj (φ e.val.out.2) (p (.inl e)).2.1)
    (hspends:∀ e:{e:V×U // H₀ e.1 e.2},Q.Adj e.val.1 (p (.inr e)).1 ∧
      Q.Adj (φ e.val.1) (p (.inr e)).1 ∧ Q.Adj e.val.1 (p (.inr e)).2.1 ∧
      Q.Adj (φ e.val.1) (p (.inr e)).2.1)
    (hHroot:∀ e,H e.val.out.1 (h e)∧H (φ e.val.out.1) (h e)∧
      H e.val.out.2 (h e)∧H (φ e.val.out.2) (h e))
    (hHT:∀ e,∀ v∈transformerHubAttachments G σ
      (transformerRimEndpoint G Q H₀ p) (transformerSpokeEndpoint G Q H₀ b p) e,H v (h e))
    (hab:∀ d:Σ v,G.neighborSet v,Q.Adj
      (transformerRimEndpoint G Q H₀ p d) (transformerSpokeEndpoint G Q H₀ b p d)):
    ∃ D:∀ d:Σ v,G.neighborSet v,
      OrdinaryVertexWheelPair Q F H 3 d.1 (φ d.1)
        (transformerRimEndpoint G Q H₀ p d) (transformerSpokeEndpoint G Q H₀ b p d)
        (transformerAssignedHub G σ h d),
      (∀ d,∀ v∈rootWheelInternal (D d).first d.1 (transformerRimEndpoint G Q H₀ p d)
          (transformerSpokeEndpoint G Q H₀ b p d),False) ∧
      (∀ d e,d≠e→Disjoint (ordinaryWheelResources (D d).first) (ordinaryWheelResources (D e).first)) ∧
      (∀ d e,d≠e→Disjoint (ordinaryWheelResources (D d).second) (ordinaryWheelResources (D e).second)) ∧
      HasOrdinaryWheelDecomposition (wheelFamilyRim (fun d=>(D d).first)) (wheelFamilySpokes (fun d=>(D d).first)) 3 ∧
      HasOrdinaryWheelDecomposition (wheelFamilyRim (fun d=>(D d).second)) (wheelFamilySpokes (fun d=>(D d).second)) 3:=by
  let a:=transformerRimEndpoint G Q H₀ p
  let z:=transformerSpokeEndpoint G Q H₀ b p
  let u:=transformerAssignedHub G σ h
  have ha (d:Σ v,G.neighborSet v):a d∈(p (.inl (rimIncidenceEquiv G d).1)).2.2.support:=
    graphPathEndpoint_mem _ _
  have hz (d:Σ v,G.neighborSet v):z d∈(p (.inr (spokeEndpointEquiv G H₀ b d).1)).2.2.support:=
    graphPathEndpoint_mem _ _
  have hgeom:=triangular_path_endpoint_geometry G Q H₀ φ hφ b σ hσ h p hrim hsp hdis
  have hgeom0:=triangular_path_endpoint_geometry G Q H₀ id (fun v w he=>he.ne) b σ hσ h p hrim hsp hdis
  change Function.Injective z∧(∀ d e,a d≠z e)∧Function.Injective (fun d:Σ v,G.neighborSet v=>(φ d.1,a d))∧
    Function.Injective (fun d=>(a d,u d)) at hgeom
  change Function.Injective z∧(∀ d e,a d≠z e)∧Function.Injective (fun d:Σ v,G.neighborSet v=>(d.1,a d))∧
    Function.Injective (fun d=>(a d,u d)) at hgeom0
  have haQ:=actual_rim_endpoint_adjacency G Q φ (fun e=>p (.inl e)) hends
  have hzQ:=actual_spoke_endpoint_adjacency G Q H₀ φ b p hspends
  have hHu:=actual_shifted_root_hub_adjacency G H φ σ h hHroot
  have hHab:=actual_shifted_endpoints_adjacent G H σ h a z hHT
  have hsmall (d:Σ v,G.neighborSet v):
      ∀ v∈({d.1,a d,z d}:Finset V),∀ w∈({d.1,a d,z d}:Finset V),¬F.Adj v w:=by
    have hra:¬F.Adj (a d) d.1:=hFR _ _ (ha d) _ (hroot d).1
    have hrz:¬F.Adj (z d) d.1:=hFR _ _ (hz d) _ (hroot d).1
    have haz:¬F.Adj (a d) (z d):=hFF _ _ _ (ha d) _ (hz d)
    intro v hv w hw
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv hw
    rcases hv with rfl|rfl|rfl <;> rcases hw with rfl|rfl|rfl
    · exact F.loopless.irrefl _
    · exact fun hh=>hra hh.symm
    · exact fun hh=>hrz hh.symm
    · exact hra
    · exact F.loopless.irrefl _
    · exact haz
    · exact hrz
    · exact fun hh=>haz hh.symm
    · exact F.loopless.irrefl _
  have existsD (d:Σ v,G.neighborSet v):
      ∃ D:OrdinaryVertexWheelPair Q F H 3 d.1 (φ d.1) (a d) (z d) (u d),
        (∀ v,v∈(ordinaryWheelRim D.first).support↔v∈({d.1,a d,z d}:Finset V)) ∧
        (∀ v,v∈(ordinaryWheelRim D.second).support↔v∈({φ d.1,a d,z d}:Finset V)) ∧
        rootWheelInternal D.first d.1 (a d) (z d)=∅:=
    triangular_vertex_wheel_pair Q F H d.1 (φ d.1) (a d) (z d) (u d) (hroot d).2.2
      (haQ d).1 (hzQ d).1 (haQ d).2 (hzQ d).2 (hab d)
      ⟨(hHu d).1,(hHu d).2,(hHab d).1,(hHab d).2⟩ (hsmall d)
      ⟨fun hh=>hFR _ _ (ha d) _ (hroot d).2.1 hh.symm,
       fun hh=>hFR _ _ (hz d) _ (hroot d).2.1 hh.symm⟩
  choose D hD using existsD
  have hxinj:Function.Injective (fun d:Σ v,G.neighborSet v=>(d.1,u d)):=
    actual_shifted_root_spokes_injective G id σ h (fun v w he=>he.ne)
  have hyinj:Function.Injective (fun d:Σ v,G.neighborSet v=>(φ d.1,u d)):=
    actual_shifted_root_spokes_injective G φ σ h hφ
  have hxa (d e:Σ v,G.neighborSet v):d.1≠a e:=fun he=>(hpW _ _ (ha e)).2 (he ▸ (hroot d).1)
  have hya (d e:Σ v,G.neighborSet v):φ d.1≠a e:=fun he=>(hpW _ _ (ha e)).2 (he ▸ (hroot d).2.1)
  have hxz (d e:Σ v,G.neighborSet v):d.1≠z e:=fun he=>(hpW _ _ (hz e)).2 (he ▸ (hroot d).1)
  have hyz (d e:Σ v,G.neighborSet v):φ d.1≠z e:=fun he=>(hpW _ _ (hz e)).2 (he ▸ (hroot d).2.1)
  have hfirst:=triangle_wheel_family_packing Q F H (fun d=>(D d).first) (fun d=>d.1) a z u
    (fun d v hv=>by simpa only [Finset.mem_insert,Finset.mem_singleton] using (hD d).1 v |>.mp hv)
    (fun d=>(D d).first_hub) hxa hxz hgeom.2.1 hgeom.1 hgeom0.2.2.1 hxinj hgeom.2.2.2
  have hsecond:=triangle_wheel_family_packing Q F H (fun d=>(D d).second) (fun d=>φ d.1) a z u
    (fun d v hv=>by simpa only [Finset.mem_insert,Finset.mem_singleton] using (hD d).2.1 v |>.mp hv)
    (fun d=>(D d).second_hub) hya hyz hgeom.2.1 hgeom.1 hgeom.2.2.1 hyinj hgeom.2.2.2
  refine ⟨D,?_,hfirst.1,hsecond.1,hfirst.2,hsecond.2⟩
  intro d v hv
  change v∈rootWheelInternal (D d).first d.1 (a d) (z d) at hv
  rw [(hD d).2.2] at hv
  exact Finset.notMem_empty _ hv

end Oberwolfach
