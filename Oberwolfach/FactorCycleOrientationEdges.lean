module

public import Oberwolfach.FactorCycleOrientation
public import Oberwolfach.CycleCopies

@[expose] public section
/-! The global cyclic permutation orients exactly the edges of a two-regular
factor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem fin_rotate_succ_iff {r:ℕ} (hr:3≤r) (i j:Fin r):
    (i.val+1)%r=j.val ↔ finRotate r i=j:=by
  letI:NeZero r:=⟨by omega⟩
  have hval:((finRotate r i):Fin r).val=(i.val+1)%r:=by
    rw [finRotate_apply,Fin.val_add,Fin.val_one']
    have hone:1%r=1:=Nat.mod_eq_of_lt (by omega)
    rw [hone]
  constructor
  · intro h
    apply Fin.ext
    exact hval.trans h
  · intro h
    have hh:=congrArg Fin.val h
    exact hval.symm.trans hh

theorem factor_cycle_orientation_adj {X:Type*} [Fintype X] [DecidableEq X]
    (G:SimpleGraph X) (hG:G.IsRegularOfDegree 2)
    (e:∀C:G.ConnectedComponent,SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph)
    (x:X):G.Adj x (factorCycleOrientation G e x):=by
  let C:=G.connectedComponentMk x
  let xc:C:=⟨x,(SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl⟩
  let j:Fin (Fintype.card C):=(e C).symm xc
  have hr:3≤Fintype.card C:=(component_regular_two_cycle_iso G hG C).1
  have hj:(SimpleGraph.cycleGraph (Fintype.card C)).Adj j (finRotate (Fintype.card C) j):=by
    apply (cycleGraph_modular_adj (by omega) _ _).2
    exact Or.inl ((fin_rotate_succ_iff hr j _).2 rfl)
  have hh:C.toSimpleGraph.Adj xc (e C (finRotate (Fintype.card C) j)):=by
    have hh':= (e C).map_rel_iff.mpr hj
    simpa [j] using hh' 
  change G.Adj x (e C (finRotate (Fintype.card C) j)).val at hh
  rw [factor_cycle_orientation_on_component G e C xc]
  exact hh

theorem factor_cycle_orientation_edge_iff {X:Type*} [Fintype X] [DecidableEq X]
    (G:SimpleGraph X) (hG:G.IsRegularOfDegree 2)
    (e:∀C:G.ConnectedComponent,SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph)
    (x y:X):G.Adj x y ↔ factorCycleOrientation G e x=y ∨ factorCycleOrientation G e y=x:=by
  constructor
  · intro hxy
    let C:=G.connectedComponentMk x
    let xc:C:=⟨x,(SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl⟩
    have hy:G.connectedComponentMk y=C:=by
      dsimp [C]
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxy).symm
    let yc:C:=⟨y,(SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr hy⟩
    let i:Fin (Fintype.card C):=(e C).symm xc
    let j:Fin (Fintype.card C):=(e C).symm yc
    have hr:3≤Fintype.card C:=(component_regular_two_cycle_iso G hG C).1
    have hc:(SimpleGraph.cycleGraph (Fintype.card C)).Adj i j:=by
      apply (e C).map_rel_iff.mp
      have hh:C.toSimpleGraph.Adj xc yc:=by
        change G.Adj x y
        exact hxy
      simpa [i,j] using hh
    rcases (cycleGraph_modular_adj (by omega) _ _).mp hc with hij | hji
    · left
      have he:finRotate (Fintype.card C) i=j:=(fin_rotate_succ_iff hr i j).mp hij
      rw [factor_cycle_orientation_on_component G e C xc]
      change (e C (finRotate (Fintype.card C) i)).val=y
      rw [he]
      simp [j,yc]
    · right
      have he:finRotate (Fintype.card C) j=i:=(fin_rotate_succ_iff hr j i).mp hji
      rw [factor_cycle_orientation_on_component G e C yc]
      change (e C (finRotate (Fintype.card C) j)).val=x
      rw [he]
      simp [i,xc]
  · rintro (h | h)
    · rw [←h]
      exact factor_cycle_orientation_adj G hG e x
    · rw [←h]
      exact (factor_cycle_orientation_adj G hG e y).symm
end Oberwolfach
