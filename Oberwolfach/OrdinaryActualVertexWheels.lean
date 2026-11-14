module

public import Oberwolfach.TransformerActualData
public import Oberwolfach.OrdinaryVertexWheelPacking

@[expose] public section

/-! Construct the vertex-wheel families from the actual rim and spoke
paths and the shifted rim-edge hubs. Endpoint disjointness and distinct
root spokes are conclusions of their incidence assignments. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

 theorem ordinary_actual_vertex_wheels (G Q F:SimpleGraph V) (H₀ H:V→U→Prop) (φ:V→V)
    (b:∀ v,G.neighborSet v≃({u:U // H₀ v u}×Fin 2))
    (σ:∀ v,Equiv.Perm (G.neighborSet v)) (h:G.edgeFinset↪U)
    (p:(G.edgeFinset⊕{e:V×U // H₀ e.1 e.2})→(Σ a:V,Σ c:V,Q.Walk a c))
    (A R W:Finset V) (hRW:R⊆W)
    (hroot:∀ d:Σ v,G.neighborSet v,d.1∈R∧φ d.1∈R∧d.1≠φ d.1)
    (hφ:∀ v w,G.Adj v w→φ v≠φ w)
    (hp:∀ i,(p i).2.2.IsPath) (hlen:∀ i,0<(p i).2.2.length)
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
    (r:ℕ) (hr:4≤r) (L t:ℝ) (hL:0≤L) (hF:∀ v,(F.degree v:ℝ)≤L)
    (hcount:∀ u v w,t≤(((A.filter (fun x=>H x u))∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))
    (hbudget:W.card+Fintype.card (Σ v,G.neighborSet v)*r+((r:ℝ)+4)*(L+1)<t):
    ∃ D:∀ d:Σ v,G.neighborSet v,
      OrdinaryVertexWheelPair Q F H r d.1 (φ d.1)
        (transformerRimEndpoint G Q H₀ p d) (transformerSpokeEndpoint G Q H₀ b p d)
        (transformerAssignedHub G σ h d),
      (∀ d,∀ v∈rootWheelInternal (D d).first d.1 (transformerRimEndpoint G Q H₀ p d)
          (transformerSpokeEndpoint G Q H₀ b p d),v∈A∧v∉W∧v≠φ d.1) ∧
      (∀ d e,d≠e→Disjoint (ordinaryWheelResources (D d).first) (ordinaryWheelResources (D e).first)) ∧
      (∀ d e,d≠e→Disjoint (ordinaryWheelResources (D d).second) (ordinaryWheelResources (D e).second)) ∧
      HasOrdinaryWheelDecomposition (wheelFamilyRim (fun d=>(D d).first)) (wheelFamilySpokes (fun d=>(D d).first)) r ∧
      HasOrdinaryWheelDecomposition (wheelFamilyRim (fun d=>(D d).second)) (wheelFamilySpokes (fun d=>(D d).second)) r:=by
  let a:=transformerRimEndpoint G Q H₀ p
  let z:=transformerSpokeEndpoint G Q H₀ b p
  let u:=transformerAssignedHub G σ h
  have ha (d:Σ v,G.neighborSet v):a d∈(p (.inl (rimIncidenceEquiv G d).1)).2.2.support:=
    graphPathEndpoint_mem _ _
  have hz (d:Σ v,G.neighborSet v):z d∈(p (.inr (spokeEndpointEquiv G H₀ b d).1)).2.2.support:=
    graphPathEndpoint_mem _ _
  have hpair:=transformer_endpoint_realization G Q H₀ b p hp hlen hdis
  change Function.Injective a∧Function.Injective z∧(∀ d e,a d≠z e)∧
    (∀ d,a d≠z d)∧(∀ d e,d≠e→Disjoint ({a d,z d}:Finset V) {a e,z e}) at hpair
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
  obtain ⟨D,hD,hint⟩:=simultaneous_ordinary_vertex_wheel_pairs Q F H
    (fun d=>A.filter (fun v=>H v (u d))) W Finset.univ (fun _=>Finset.subset_univ _)
    (fun d:Σ v,G.neighborSet v=>d.1) (fun d=>φ d.1) a z u
    (fun d=>(hroot d).2.2) hpair.2.2.2.1 (fun _=>Finset.mem_univ _) (fun _=>Finset.mem_univ _)
    (fun d=>(haQ d).1) (fun d=>(hzQ d).1) (fun d=>(haQ d).2) (fun d=>(hzQ d).2)
    hsmall (fun d=>⟨fun hh=>hFR _ _ (ha d) _ (hroot d).2.1 hh.symm,
      fun hh=>hFR _ _ (hz d) _ (hroot d).2.1 hh.symm⟩)
    (fun d=>⟨(hHu d).1,(hHu d).2,(hHab d).1,(hHab d).2⟩)
    (fun _ _ hv=>(Finset.mem_filter.mp hv).2) r hr L t hL hF
    (fun d v _ w _=>hcount (u d) v w) hbudget
  have hxinj:Function.Injective (fun d:Σ v,G.neighborSet v=>(d.1,u d)):=
    actual_shifted_root_spokes_injective G id σ h (fun v w ha=>ha.ne)
  have hyinj:Function.Injective (fun d:Σ v,G.neighborSet v=>(φ d.1,u d)):=
    actual_shifted_root_spokes_injective G φ σ h hφ
  have hpacking:=ordinary_vertex_wheel_packing Q F H r (fun d:Σ v,G.neighborSet v=>d.1)
    (fun d=>φ d.1) a z u D R W hRW (fun d=>(hroot d).1) (fun d=>(hroot d).2.1)
    (fun d=>hpW _ _ (ha d)) (fun d=>hpW _ _ (hz d)) hpair.2.2.2.2
    (fun d v hv=>(hD d v hv).2.1) hint hxinj hyinj
  refine ⟨D,?_,hpacking.1,hpacking.2.1,hpacking.2.2.1,hpacking.2.2.2⟩
  intro d v hv
  have hh:=hD d v hv
  exact ⟨(Finset.mem_filter.mp hh.1).1,hh.2⟩

end Oberwolfach
