module

public import Oberwolfach.RegularTwoBufferedPathSeparation

@[expose] public section
/-! Internal vertices of a buffered path have exactly their two path neighbours. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem regular_two_buffered_inner_neighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) (hG:G.IsRegularOfDegree 2) (n:ℕ)
    (ext:Fin (n+5)↪V) (inner:Fin (n+1)↪V)
    (hinner:∀k,inner k=ext ⟨k.val+2,by omega⟩)
    (hstep:∀k:Fin (n+4),G.Adj (ext ⟨k.val,by omega⟩) (ext ⟨k.val+1,by omega⟩))
    (p:Fin (n+1)) (y:V) (hy:G.Adj (inner p) y) :
    y=ext ⟨p.val+1,by omega⟩ ∨ y=ext ⟨p.val+3,by omega⟩ := by
  classical
  let u:=ext ⟨p.val+1,by omega⟩
  let v:=ext ⟨p.val+3,by omega⟩
  have hu:G.Adj (inner p) u:=by
    rw [hinner p]
    exact (hstep ⟨p.val+1,by omega⟩).symm
  have hv:G.Adj (inner p) v:=by
    rw [hinner p]
    exact hstep ⟨p.val+2,by omega⟩
  have huv:u≠v:=by
    intro h
    have hh:(⟨p.val+1,by omega⟩:Fin (n+5))=⟨p.val+3,by omega⟩:=ext.injective h
    have hhval:p.val+1=p.val+3:=congrArg Fin.val hh
    omega
  have hsub:({u,v}:Finset V)⊆G.neighborFinset (inner p):=by
    intro z hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl|rfl <;> simpa using (show G.Adj (inner p) _ from by first | exact hu | exact hv)
  have hcard:(G.neighborFinset (inner p)).card=2:=by simpa using hG (inner p)
  have heq:G.neighborFinset (inner p)={u,v}:=by
    apply (Finset.eq_of_subset_of_card_le hsub ?_).symm
    simpa [huv,hcard]
  have hymem:y∈G.neighborFinset (inner p):=by simpa using hy
  rw [heq] at hymem
  simpa only [Finset.mem_insert,Finset.mem_singleton] using hymem

theorem regular_two_buffered_strict_inner_neighbor
    {V : Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) (hG:G.IsRegularOfDegree 2) (n:ℕ)
    (ext:Fin (n+5)↪V) (inner:Fin (n+1)↪V)
    (hinner:∀k,inner k=ext ⟨k.val+2,by omega⟩)
    (hstep:∀k:Fin (n+4),G.Adj (ext ⟨k.val,by omega⟩) (ext ⟨k.val+1,by omega⟩))
    (p:Fin (n+1)) (hp0:0<p.val) (hpn:p.val<n) (y:V) (hy:G.Adj (inner p) y) :
    ∃q:Fin (n+1),y=inner q ∧ (q.val+1=p.val ∨ q.val=p.val+1) := by
  rcases regular_two_buffered_inner_neighbors G hG n ext inner hinner hstep p y hy with hleft|hright
  · let q:Fin (n+1):=⟨p.val-1,by omega⟩
    refine ⟨q,?_,Or.inl (by dsimp [q];omega)⟩
    rw [hleft,hinner q]
    congr 1
    apply Fin.ext
    dsimp [q]
    omega
  · let q:Fin (n+1):=⟨p.val+1,by omega⟩
    refine ⟨q,?_,Or.inr rfl⟩
    rw [hright,hinner q]
end Oberwolfach
