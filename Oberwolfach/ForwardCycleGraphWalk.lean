module

public import Oberwolfach.CyclicCoordinates
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph

@[expose] public section
/-! A cyclic graph has a simple closed walk that follows `finRotate`. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem forward_cycle_graph_walk (N:ℕ) (hN:3≤N):
    ∃(z:Fin N) (p:(SimpleGraph.cycleGraph N).Walk z z),p.IsCycle ∧ p.length=N ∧
      ∀k<p.length,finRotate N (p.getVert k)=p.getVert (k+1):=by
  obtain ⟨m,hm⟩:=Nat.exists_eq_add_of_le hN
  have hm':N=m+3:=by omega
  rw [hm']
  let p:=(SimpleGraph.cycleGraph.cycle m).reverse
  have hp:∀k≤m+3,p.getVert k=⟨k%(m+3),Nat.mod_lt _ (by omega)⟩:=by
    intro k hk
    dsimp only [p]
    rw [SimpleGraph.Walk.getVert_reverse,SimpleGraph.cycleGraph.length_cycle,
      SimpleGraph.cycleGraph.getVert_cycle (by omega)]
    congr 1
    have hh:m+3-(m+3-k)=k:=by omega
    rw [hh]
  refine ⟨0,p,SimpleGraph.cycleGraph.isCycle_cycle.reverse,by simp [p],?_⟩
  intro k hk
  have hk':k<m+3:=by simpa [p] using hk
  rw [hp k (by omega),hp (k+1) (by omega),finRotate_apply]
  apply Fin.ext
  simp only [Fin.val_add,Fin.val_mk,Fin.val_one]
  rw [Nat.mod_eq_of_lt hk']
end Oberwolfach
