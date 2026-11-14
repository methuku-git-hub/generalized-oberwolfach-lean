module

public import Oberwolfach.OrdinaryTwoDomainChangeGeometry
public import Oberwolfach.OrdinaryEmbeddedPairDegrees

@[expose] public section
/-! Root stars, support and balance in the auxiliary sum graph are exactly
those of the original rim and hub domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_sum_rim_full_neighbours (Q:SimpleGraph V) (v:V):
    (Q.map (⟨Sum.inl,Sum.inl_injective⟩:V↪V⊕U)).neighborFinset (Sum.inl v)=
      (Q.neighborFinset v).image Sum.inl:=by
  ext z
  cases z with
  | inl w=>
    simp [SimpleGraph.mem_neighborFinset]
    change (Q.map (⟨Sum.inl,Sum.inl_injective⟩:V↪V⊕U)).Adj
      ((⟨Sum.inl,Sum.inl_injective⟩:V↪V⊕U) v) ((⟨Sum.inl,Sum.inl_injective⟩:V↪V⊕U) w) ↔ _
    exact SimpleGraph.map_adj_apply
  | inr u=>
    simp [SimpleGraph.mem_neighborFinset]
    intro hadj
    obtain ⟨a,b,hab,ha,hb⟩:=(SimpleGraph.map_adj (⟨Sum.inl,Sum.inl_injective⟩:V↪V⊕U) Q _ _).mp hadj
    cases hb

theorem ordinary_sum_hosts_supported (Q:SimpleGraph V) (J:V→U→Prop) (B:Finset U):
    let e:V↪V⊕U:=⟨Sum.inl,Sum.inl_injective⟩
    let f:B↪V⊕U:=⟨fun u=>Sum.inr u.val,by intro a b h;exact Subtype.ext (Sum.inr.inj h)⟩
    let Q':=Q.map e
    let J':=ordinaryPhysicalSpokeGraph (fun v u=>u∈B∧J v u);
    (∀v w,Q'.Adj v w→v∈Set.range e ∧ w∈Set.range e) ∧
    (∀v∈Set.range e,∀u,J'.Adj v u→u∈Set.range f) ∧
    (∀v u,J'.Adj (e v) (f u) ↔ J v u.val) ∧
    (∀v∈ordinarySumRimSet (V:=V) (U:=U),J'.neighborFinset v⊆ordinarySumHubSet (V:=V) B):=by
  intro e f Q' J'
  refine ⟨?_,?_,?_,?_⟩
  · intro v w h
    obtain ⟨a,b,hab,ha,hb⟩:=(SimpleGraph.map_adj e Q _ _).mp h
    exact ⟨⟨a,ha⟩,⟨b,hb⟩⟩
  · intro v hv u hu
    obtain ⟨a,rfl⟩:=hv
    cases u with
    | inl b=>change False at hu;exact hu.elim
    | inr b=>
      have hb:b∈B:=hu.1
      exact ⟨⟨b,hb⟩,rfl⟩
  · intro v u
    change (u.val∈B∧J v u.val)↔J v u.val
    simp [u.property]
  · intro v hv u hu
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hv
    cases u with
    | inl b=>simp [J',ordinaryPhysicalSpokeGraph,ordinaryPhysicalGraph,SimpleGraph.mem_neighborFinset] at hu
    | inr b=>
      have hb:b∈B:=((J'.mem_neighborFinset (Sum.inl a) (Sum.inr b)).mp hu).1
      exact Finset.mem_image.mpr ⟨b,hb,rfl⟩

theorem ordinary_sum_spoke_root_degree (J:V→U→Prop) (B:Finset U) (v:V)
    (hroot:∀u,J v u→u∈B):
    (ordinaryPhysicalSpokeGraph (fun v u=>u∈B∧J v u)).degree (Sum.inl v)=
      (Finset.univ.filter (J v)).card:=by
  have hh:=ordinary_physical_degree_row (⊥:SimpleGraph V) (fun v u=>u∈B∧J v u) v
  have hf:Finset.univ.filter (fun u=>u∈B∧J v u)=Finset.univ.filter (J v):=by
    ext u
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨And.right,fun h=>⟨hroot u h,h⟩⟩
  have hb:((⊥:SimpleGraph V).neighborSet v).ncard=0:=by simp
  simp only [←SimpleGraph.ncard_neighborSet] at hh ⊢
  rw [hb,zero_add] at hh
  have hh':((ordinaryPhysicalSpokeGraph (fun v u=>u∈B∧J v u)).neighborSet (Sum.inl v)).ncard=
      (Finset.univ.filter (fun u=>u∈B∧J v u)).card:=by
    convert hh using 1 <;> congr! 8 <;> first | rfl | exact Subsingleton.elim _ _
  have hc:=congrArg Finset.card hf
  exact hh'.trans hc
end Oberwolfach
