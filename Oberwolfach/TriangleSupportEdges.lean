module

public import Oberwolfach.TriangleCyclesFromMatchings

@[expose] public section

/-! An actual embedded triangle contains precisely the non-loop pairs
of its support. This identifies physical edges when an endpoint factor
is completed by adjoining its external root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem IsEmbeddedCycle.triangle_adj {G : SimpleGraph V} (hG : IsEmbeddedCycle G 3) (x y : V) :
    G.Adj x y ↔ x∈G.support ∧ y∈G.support ∧ x≠y := by
  constructor
  · intro h;exact ⟨h.mem_support_left,h.mem_support_right,h.ne⟩
  · obtain ⟨_,f,rfl⟩:=hG
    rw [cycle_map_support (by norm_num : 3≤3) f]
    rintro ⟨⟨i,rfl⟩,⟨j,rfl⟩,hne⟩
    have hij : i≠j:=fun h=>hne (congrArg f h)
    apply (SimpleGraph.map_adj f _ _ _).mpr
    refine ⟨i,j,?_,rfl,rfl⟩
    fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | decide

theorem triangle_cycle_from_vertices_support (G : SimpleGraph V) (x v w : V)
    (hxv : x≠v) (hxw : x≠w) (hvw : v≠w)
    (hxvG : G.Adj x v) (hxwG : G.Adj x w) (hvwG : G.Adj v w) :
    ∃ C : OrdinaryCycle G 3,C.val.val.support.toFinset={x,v,w} := by
  obtain ⟨C,hC⟩:=triangle_cycle_from_vertices G x v w hxv hxw hvw hxvG hxwG hvwG
  refine ⟨C,hC.trans ?_⟩
  ext z
  simp only [Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨i,rfl⟩;fin_cases i <;> simp
  · rintro (rfl|rfl|rfl)
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩

end Oberwolfach
