module

public import Oberwolfach.OrdinaryVertexWheelPairs
public import Oberwolfach.OrdinaryWheelDisjointness
public import Oberwolfach.EmbeddedCycleTriangleFree

@[expose] public section

/-! The edge-wheel/vertex-wheel intersection check. A vertex wheel meets
an earlier wheel only at its two prescribed endpoints; the missing rim
edge between those endpoints is proved from the cycle length. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {Q F:SimpleGraph V} {H:V→U→Prop} {r:ℕ}

 theorem edge_vertex_wheels_disjoint (W C:OrdinaryWheel Q F H r) (hr:4≤r)
    (x a b:V) (hxa:(ordinaryWheelRim C).Adj x a) (hxb:(ordinaryWheelRim C).Adj x b)
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
  have hnab:¬(ordinaryWheelRim C).Adj a b:=
    fun hab=>(show IsEmbeddedCycle (ordinaryWheelRim C) r from C.val.1.val.property).no_triangle
      hr x a b hxa hab hxb.symm
  apply (ordinaryWheelResources_disjoint_iff W C).mpr
  constructor
  · apply disjoint_iff_inf_le.mpr
    intro v w h
    rcases hsplit v h.2.mem_support_left h.1.mem_support_left with hv|hv <;>
      rcases hsplit w h.2.mem_support_right h.1.mem_support_right with hw|hw
    · exact (h.2.ne (hv.trans hw.symm)).elim
    · exact (hnab (hv ▸ hw ▸ h.2)).elim
    · exact (hnab (hw ▸ hv ▸ h.2.symm)).elim
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

 theorem vertex_pair_internal_second
    {x y a b:V} {u:U} (D:OrdinaryVertexWheelPair Q F H r x y a b u)
    (havoid:∀ v∈rootWheelInternal D.first x a b,v≠y):
    rootWheelInternal D.second y a b=rootWheelInternal D.first x a b:=by
  ext v
  constructor
  · intro hv
    have hv':v∈(ordinaryWheelRim D.second).support∧v∉({y,a,b}:Finset V):=by
      simpa only [rootWheelInternal,Finset.mem_sdiff,Set.mem_toFinset] using hv
    rcases (D.second_support v).mp hv'.1 with he|h
    · exact (hv'.2 (by simp [he])).elim
    · simp only [rootWheelInternal,Finset.mem_sdiff,Set.mem_toFinset,Finset.mem_insert,Finset.mem_singleton]
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hv'
      exact ⟨h.1,by tauto⟩
  · intro hv
    have hvy:=havoid v hv
    have hv':v∈(ordinaryWheelRim D.first).support∧v∉({x,a,b}:Finset V):=by
      simpa only [rootWheelInternal,Finset.mem_sdiff,Set.mem_toFinset] using hv
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hv'
    simp only [rootWheelInternal,Finset.mem_sdiff,Set.mem_toFinset,Finset.mem_insert,Finset.mem_singleton]
    exact ⟨(D.second_support v).mpr (Or.inr ⟨hv'.1,hv'.2.1⟩),by tauto⟩

end Oberwolfach
