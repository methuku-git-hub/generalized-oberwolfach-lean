module

public import Oberwolfach.PairEdgeDegree

@[expose] public section

/-! The simple graph determined by a finite family of physical edges.
An incidence-cardinality bound implies the ordinary graph degree bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

def physicalEdgeGraph (S : Finset (Finset V)) : SimpleGraph V where
  Adj x y := x≠y ∧ ({x,y}:Finset V)∈S
  symm := ⟨by intro x y h;exact ⟨h.1.symm,by simpa only [Finset.pair_comm] using h.2⟩⟩
  loopless := ⟨by intro x h;exact h.1 rfl⟩

theorem physicalEdgeGraph_degree_le_incident (S : Finset (Finset V)) (v : V) :
    (physicalEdgeGraph S).degree v≤(S.filter (fun e => v∈e)).card := by
  let G := physicalEdgeGraph S
  let f : {u : V // G.Adj v u} → S.filter (fun e => v∈e) := fun u =>
    ⟨{v,u.val},Finset.mem_filter.mpr ⟨u.property.2,by simp⟩⟩
  have hf : Function.Injective f := by
    intro u w he
    apply Subtype.ext
    have hp : ({v,u.val}:Finset V)={v,w.val} := congrArg Subtype.val he
    have hu : u.val∈({v,w.val}:Finset V) := by rw [← hp];simp
    rcases Finset.mem_insert.mp hu with hv|hu
    · exact (u.property.1 hv.symm).elim
    · exact Finset.mem_singleton.mp hu
  have hh := Fintype.card_le_of_injective f hf
  have he : Fintype.card {u : V // G.Adj v u}=G.degree v := by
    convert G.card_neighborSet_eq_degree v using 1 <;> congr!
  rw [he,Fintype.card_coe] at hh
  exact hh

end Oberwolfach
