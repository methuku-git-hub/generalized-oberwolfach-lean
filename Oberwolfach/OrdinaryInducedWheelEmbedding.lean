module

public import Oberwolfach.OrdinaryCycleInEmbeddedDomain
public import Oberwolfach.OrdinaryWheelLoads

@[expose] public section
/-! A wheel supported on selected vertex and hub domains descends to the
induced host, retaining its actual rim graph and hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_supported_wheel_induced_rim (Q F:SimpleGraph V) (H:V→U→Prop)
    (A:Finset V) (r:ℕ) (W:OrdinaryWheel Q F H r)
    (hA:(ordinaryWheelRim W).support⊆A):
    ∃D:SimpleGraph A,IsEmbeddedCycle D r ∧ D≤Q.induce (A:Set V) ∧
      D.map (Function.Embedding.subtype (fun v=>v∈(A:Set V)))=ordinaryWheelRim W:=by
  let φ:A↪V:=Function.Embedding.subtype (fun v=>v∈(A:Set V))
  have hhost:ordinaryWheelRim W≤(Q.induce (A:Set V)).map φ:=by
    intro x y hxy
    have hx:x∈A:=hA hxy.mem_support_left
    have hy:y∈A:=hA hxy.mem_support_right
    have hh:(Q.induce (A:Set V)).Adj ⟨x,hx⟩ ⟨y,hy⟩:=W.val.1.property hxy
    exact SimpleGraph.map_adj_apply.mpr hh
  exact ordinary_cycle_in_embedded_domain φ (Q.induce (A:Set V)) (ordinaryWheelRim W) r W.val.1.val.property hhost

def ordinaryInducedWheel (Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U) (r:ℕ)
    (W:{W:OrdinaryWheel Q F H r // (ordinaryWheelRim W).support⊆A ∧ ordinaryWheelHub W∈B}):
    OrdinaryWheel (Q.induce (A:Set V)) (F.induce (A:Set V)) (fun (v:A) (u:B)=>H v.val u.val) r:=by
  let D:=Classical.choose (ordinary_supported_wheel_induced_rim Q F H A r W.val W.property.1)
  have hD:=Classical.choose_spec (ordinary_supported_wheel_induced_rim Q F H A r W.val W.property.1)
  have hs (v:A) (hv:v∈D.support):v.val∈(ordinaryWheelRim W.val).support:=by
    rw [←hD.2.2,SimpleGraph.support_map]
    exact ⟨v,hv,rfl⟩
  exact ⟨(⟨⟨D,hD.1⟩,hD.2.1⟩,⟨ordinaryWheelHub W.val,W.property.2⟩),
    (fun v hv=>W.val.property.1 v.val (hs v hv)),
    (fun v hv w hw=>W.val.property.2 v.val (hs v hv) w.val (hs w hw))⟩

theorem ordinary_induced_wheel_rim_map (Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U) (r:ℕ)
    (W:{W:OrdinaryWheel Q F H r // (ordinaryWheelRim W).support⊆A ∧ ordinaryWheelHub W∈B}):
    (ordinaryWheelRim (ordinaryInducedWheel Q F H A B r W)).map
      (Function.Embedding.subtype (fun v=>v∈(A:Set V)))=ordinaryWheelRim W.val:=by
  exact (Classical.choose_spec (ordinary_supported_wheel_induced_rim Q F H A r W.val W.property.1)).2.2

theorem ordinary_induced_wheel_injective (Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U) (r:ℕ):
    Function.Injective (ordinaryInducedWheel Q F H A B r):=by
  intro W Z h
  apply Subtype.ext
  have hrim:ordinaryWheelRim W.val=ordinaryWheelRim Z.val:=by
    have hh:=congrArg (fun C=>(ordinaryWheelRim C).map (Function.Embedding.subtype (fun v=>v∈(A:Set V)))) h
    rw [ordinary_induced_wheel_rim_map,ordinary_induced_wheel_rim_map] at hh
    exact hh
  have hhub:ordinaryWheelHub W.val=ordinaryWheelHub Z.val:=by
    have hh:=congrArg (fun C=>(ordinaryWheelHub C).val) h
    exact hh
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    apply Subtype.ext
    exact hrim
  · exact hhub
end Oberwolfach
