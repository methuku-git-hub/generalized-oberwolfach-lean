module

public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section
/-! The induced edges inside a buffered path in a 2-regular graph join
consecutive indices; a matching target path therefore gives a local graph map. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem regular_two_buffered_path_adjacent_indices
    {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) (hG:G.IsRegularOfDegree 2) (n:ℕ)
    (ext:Fin (n+5)↪V) (inner:Fin (n+1)↪V)
    (hinner:∀k,inner k=ext ⟨k.val+2,by omega⟩)
    (hstep:∀k:Fin (n+4),G.Adj (ext ⟨k.val,by omega⟩) (ext ⟨k.val+1,by omega⟩)):
    ∀p q:Fin (n+1),G.Adj (inner p) (inner q)→p.val+1=q.val ∨ q.val+1=p.val := by
  classical
  intro p q hadj
  let x:=inner p
  let y:=inner q
  let u:=ext ⟨p.val+1,by omega⟩
  let v:=ext ⟨p.val+3,by omega⟩
  have hx:x=ext ⟨p.val+2,by omega⟩:=hinner p
  have hxu:G.Adj x u:=by rw [hx];exact (hstep ⟨p.val+1,by omega⟩).symm
  have hxv:G.Adj x v:=by rw [hx];exact hstep ⟨p.val+2,by omega⟩
  have huv:u≠v:=by
    intro h
    have hh:(⟨p.val+1,by omega⟩:Fin (n+5))=⟨p.val+3,by omega⟩:=ext.injective h
    have hh':p.val+1=p.val+3:=congrArg Fin.val hh
    omega
  have hsub:({u,v}:Finset V)⊆G.neighborFinset x:=by
    intro z hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl|rfl <;> simpa using (show G.Adj x _ from by first | exact hxu | exact hxv)
  have hcard:(G.neighborFinset x).card=2:=by simpa using hG x
  have heq:G.neighborFinset x={u,v}:=by
    apply (Finset.eq_of_subset_of_card_le hsub ?_).symm
    simp [hcard,huv]
  have hyn:y∈G.neighborFinset x:=by simpa using hadj
  rw [heq] at hyn
  simp only [Finset.mem_insert,Finset.mem_singleton] at hyn
  rcases hyn with hu|hv
  · have he:ext ⟨q.val+2,by omega⟩=ext ⟨p.val+1,by omega⟩:=by simpa only [y,u,hinner] using hu
    have hv':q.val+2=p.val+1:=congrArg Fin.val (ext.injective he)
    omega
  · have he:ext ⟨q.val+2,by omega⟩=ext ⟨p.val+3,by omega⟩:=by simpa only [y,v,hinner] using hv
    have hv':q.val+2=p.val+3:=congrArg Fin.val (ext.injective he)
    omega
end Oberwolfach
