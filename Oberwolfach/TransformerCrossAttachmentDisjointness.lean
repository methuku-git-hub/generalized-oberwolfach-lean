module

public import Oberwolfach.OrdinaryVertexWheelPairs
public import Oberwolfach.OrdinaryWheelDisjointness
public import Oberwolfach.TransformerCrossWheelDisjointness

@[expose] public section

/-! Cross-family disjointness when the edge between the two reused
attachments is absent from the earlier wheel. This version includes
triangular vertex wheels, where that edge is present in the new wheel. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {Q F:SimpleGraph V} {H:V→U→Prop} {r:ℕ}

 theorem edge_vertex_wheels_disjoint_without_attachment (W C:OrdinaryWheel Q F H r)
    (x a b:V) (hxa:(ordinaryWheelRim C).Adj x a) (hxb:(ordinaryWheelRim C).Adj x b)
    (hnab:¬(ordinaryWheelRim W).Adj a b)
    (hx:x∉(ordinaryWheelRim W).support)
    (hint:∀ v∈rootWheelInternal C x a b,v∉(ordinaryWheelRim W).support)
    (ha:Sum.inr (a,ordinaryWheelHub C)∉ordinaryWheelResources W)
    (hb:Sum.inr (b,ordinaryWheelHub C)∉ordinaryWheelResources W):
    Disjoint (ordinaryWheelResources W) (ordinaryWheelResources C):=by
  have hsplit (v:V) (hv:v∈(ordinaryWheelRim C).support)
      (hw:v∈(ordinaryWheelRim W).support):v=a∨v=b:=by
    by_contra hn
    have hn':v≠a∧v≠b:=by tauto
    have hvx:v≠x:=by intro he;exact hx (he ▸ hw)
    have hi:v∈rootWheelInternal C x a b:=by
      simp only [rootWheelInternal,Finset.mem_sdiff,Set.mem_toFinset,Finset.mem_insert,Finset.mem_singleton]
      exact ⟨hv,by tauto⟩
    exact hint v hi hw
  apply (ordinaryWheelResources_disjoint_iff W C).mpr
  constructor
  · apply disjoint_iff_inf_le.mpr
    intro v w h
    rcases hsplit v h.2.mem_support_left h.1.mem_support_left with hv|hv <;>
      rcases hsplit w h.2.mem_support_right h.1.mem_support_right with hw|hw
    · exact (h.2.ne (hv.trans hw.symm)).elim
    · exact (hnab (hv ▸ hw ▸ h.1)).elim
    · exact (hnab (hw ▸ hv ▸ h.1.symm)).elim
    · exact (h.2.ne (hv.trans hw.symm)).elim
  · intro he
    apply Finset.disjoint_left.mpr
    intro v hv hw
    have hv':v∈(ordinaryWheelRim W).support:=Set.mem_toFinset.mp hv
    have hw':v∈(ordinaryWheelRim C).support:=Set.mem_toFinset.mp hw
    have hs:Sum.inr (v,ordinaryWheelHub C)∈ordinaryWheelResources W:=
      (ordinaryWheelResources_spoke W v _).mpr ⟨he,hv'⟩
    rcases hsplit v hw' hv' with h|h
    · exact ha (h ▸ hs)
    · exact hb (h ▸ hs)


end Oberwolfach
