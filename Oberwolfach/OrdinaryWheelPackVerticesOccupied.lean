module

public import Oberwolfach.OrdinaryMarkedTupleVertexInRim

@[expose] public section

/-! Covering a wheel pack's rim endpoints covers the vertices of each of
its marked and ordinary wheels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_wheel_pack_vertices_occupied
    {V U E L I:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype I]
    {tail head:E→V} {ktail khead:L→V} {m b:ℕ} {π:Equiv.Perm V} {H₀ Hₖ:V→U→Prop}
    (len:I→ℕ) (M:Finset (MarkedWheel tail head ktail khead m π b H₀ Hₖ))
    (Q:∀i,OrderedOrdinaryWheel (U:=U) π b (len i)) (Old:Finset V)
    (hOld:∀edge∈mixedWheelRimPack len M Q,∀v∈edge,v∈Old):
    (∀W∈M,∀i:Fin (m+1),W.1.val i∈Old) ∧
    (∀j (i:Fin (len j)),(Q j).1.val i∈Old) :=by
  constructor
  · intro W hW i
    obtain ⟨edge,he,hv⟩:=ordinary_marked_tuple_vertex_in_rim tail head ktail khead m π b W.1 i
    apply hOld edge ?_ _ hv
    simp only [mixedWheelRimPack,Finset.mem_union,Finset.mem_biUnion]
    exact Or.inl ⟨W,hW,he⟩
  · intro j i
    let edge:Finset V:={(Q j).1.val i,(Q j).1.val (cycleNext i)}
    apply hOld edge ?_ _ (by simp [edge])
    simp only [mixedWheelRimPack,Finset.mem_union,Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_image]
    exact Or.inr ⟨j,i,rfl⟩
end Oberwolfach
