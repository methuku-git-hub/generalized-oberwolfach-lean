module

public import Oberwolfach.EndpointTriangleCoordinates
public import Oberwolfach.EndpointHostGraph
public import Oberwolfach.TriangleSupportEdges
public import Oberwolfach.OrdinaryWheelResources

@[expose] public section

/-! Complete an actual endpoint triangle to a physical three-wheel by
adjoining the external root. The index becomes the hub; the two row
vertices and the root form the rim triangle. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 2400000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem endpoint_triangle_root_wheel (Q H F : SimpleGraph V) (A B S T : Finset V)
    (hAB : Disjoint A B) (hSA : S⊆A) (hTB : T⊆B) (x : V)
    (hS : ∀ v∈S,Q.Adj x v ∧ ¬F.Adj x v) (hT : ∀ u∈T,H.Adj x u)
    (C : EndpointTriangle (endpointHostGraph Q H A B) F S T) :
    ∃ W : OrdinaryWheel Q F H.Adj 3,
      ordinaryWheelHub W=endpointTriangleIndex C ∧
      (ordinaryWheelRim W).support.toFinset=insert x (C.val∩S) := by
  obtain ⟨v,w,hvw,hrows⟩:=Finset.card_eq_two.mp C.property.2.1
  have hv : v∈C.val ∧ v∈S:=Finset.mem_inter.mp (by rw [hrows];simp)
  have hw : w∈C.val ∧ w∈S:=Finset.mem_inter.mp (by rw [hrows];simp)
  let u:=endpointTriangleIndex C
  have hu : u∈C.val ∧ u∈T:=endpointTriangleIndex_mem C
  have huv : u≠v:=fun he=>Finset.disjoint_left.mp hAB (he ▸ hSA hv.2) (hTB hu.2)
  have huw : u≠w:=fun he=>Finset.disjoint_left.mp hAB (he ▸ hSA hw.2) (hTB hu.2)
  have hvwQ : Q.Adj v w:=(endpointHostGraph_row Q H A B hAB (hSA hv.2) (hSA hw.2)).mp
    (C.property.2.2.2.1 v hv.1 w hw.1 hvw)
  have hvuH : H.Adj v u:=(endpointHostGraph_spoke Q H A B hAB (hSA hv.2) (hTB hu.2)).mp
    (C.property.2.2.2.1 v hv.1 u hu.1 huv.symm)
  have hwuH : H.Adj w u:=(endpointHostGraph_spoke Q H A B hAB (hSA hw.2) (hTB hu.2)).mp
    (C.property.2.2.2.1 w hw.1 u hu.1 huw.symm)
  have hxvQ:=(hS v hv.2).1
  have hxwQ:=(hS w hw.2).1
  have hxvF:=(hS v hv.2).2
  have hxwF:=(hS w hw.2).2
  have hvwF:=C.property.2.2.2.2 v hv.1 w hw.1
  obtain ⟨D,hD⟩:=triangle_cycle_from_vertices_support Q x v w hxvQ.ne hxwQ.ne hvw hxvQ hxwQ hvwQ
  have hsupp (z : V) : z∈D.val.val.support ↔ z=x ∨ z=v ∨ z=w := by
    rw [←Set.mem_toFinset,hD];simp
  have hH : ∀ z∈D.val.val.support,H.Adj z u := by
    intro z hz
    rcases (hsupp z).mp hz with rfl|rfl|rfl
    · exact hT u hu.2
    · exact hvuH
    · exact hwuH
  have hF : ∀ a∈D.val.val.support,∀ b∈D.val.val.support,¬F.Adj a b := by
    intro a ha b hb
    have hvxF : ¬F.Adj v x:=fun h=>hxvF h.symm
    have hwxF : ¬F.Adj w x:=fun h=>hxwF h.symm
    have hwvF : ¬F.Adj w v:=fun h=>hvwF h.symm
    rcases (hsupp a).mp ha with rfl|rfl|rfl <;>
      rcases (hsupp b).mp hb with rfl|rfl|rfl <;> simp_all
  refine ⟨⟨(D,u),hH,hF⟩,rfl,?_⟩
  change D.val.val.support.toFinset=insert x (C.val∩S)
  rw [hD,hrows]

end Oberwolfach
