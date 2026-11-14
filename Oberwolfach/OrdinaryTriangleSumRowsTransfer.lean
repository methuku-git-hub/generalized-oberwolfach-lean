module

public import Oberwolfach.OrdinaryBipartiteRowFamilyTransfer
public import Oberwolfach.OrdinaryTwoDomainHostGeometry
public import Oberwolfach.OrdinaryTwoDomainConflict
public import Oberwolfach.HubDomainWheels

@[expose] public section
/-! Restrict the auxiliary triangle row covers to the original domains and
then lift the selected hub subtype back to the full original hub type. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_triangle_sum_rows_transfer (Q F:SimpleGraph V) (J:V→U→Prop)
    (π:Equiv.Perm V) (σ:Equiv.Perm (V⊕U)) (d D n:ℕ)
    (hcomm:∀v,Sum.inl (π v)=σ (Sum.inl v))
    (hF:permutationConflictGraph π (3*d)≤F) (hD:∀v,F.degree v≤D)
    (B:Finset U) (Z:Finset V) (x:Fin n→V) (hJ:∀i u,J (x i) u→u∈B):
    let e:V↪V⊕U:=⟨Sum.inl,Sum.inl_injective⟩
    let f:B↪V⊕U:=⟨fun u=>Sum.inr u.val,by intro a b h;exact Subtype.ext (Sum.inr.inj h)⟩
    let Q':=Q.map e
    let F':=ordinaryTwoDomainConflict F σ (3*d)
    let J':=ordinaryPhysicalSpokeGraph (fun v u=>u∈B∧J v u);
    ∀ M:Fin n→Finset (OrdinaryWheel Q' F' J'.Adj 3),
      (∀i,OrdinaryRowCover (M i) (e (x i)) (Z.image e) 0) →
      (∀i k,i≠k→Disjoint ((M i).biUnion ordinaryWheelResources) ((M k).biUnion ordinaryWheelResources)) →
    ∃ N:Fin n→Finset (OrdinaryWheel Q F J 3),
      (∀i,OrdinaryRowCover (N i) (x i) Z 0) ∧
      (∀i k,i≠k→Disjoint ((N i).biUnion ordinaryWheelResources) ((N k).biUnion ordinaryWheelResources)):=by
  intro e f Q' F' J' M hM hcross
  have hs:=ordinary_sum_hosts_supported Q J B
  have hQeq:Q'.comap e=Q:=by ext v w;exact SimpleGraph.map_adj_apply
  have hFeq:F'.comap e=F:=(ordinary_two_domain_conflict_properties F π σ (3*d) D hcomm hF hD).2.1
  have hSeq:(fun v (u:B)=>J'.Adj (e v) (f u))=(fun v (u:B)=>J v u.val):=by
    funext v u;apply propext;exact hs.2.2.1 v u
  have hfam:=ordinary_bipartite_row_family_transfer e f Q' F' J'.Adj 3 n hs.1 hs.2.1 M x Z 0 hM hcross
  have hfam':∃ C:Fin n→Finset (OrdinaryWheel Q F (fun v (u:B)=>J v u.val) 3),
      (∀i,OrdinaryRowCover (C i) (x i) Z 0) ∧
      (∀i k,i≠k→Disjoint ((C i).biUnion ordinaryWheelResources) ((C k).biUnion ordinaryWheelResources)):=by
    rw [←hQeq,←hFeq,←hSeq]
    obtain ⟨C,hC,hcross',hres⟩:=hfam
    exact ⟨C,hC,hcross'⟩
  obtain ⟨C,hC,hcross'⟩:=hfam'
  refine ⟨fun i=>ordinaryHubDomainPacking B (C i),?_,?_⟩
  · intro i
    exact ordinaryRowCover_of_hub_domain B (C i) (x i) Z 0 (hC i) (hJ i)
  · intro i k hik
    exact ordinaryHubDomainPacking_disjoint B (C i) (C k) (hcross' i k hik)
end Oberwolfach
