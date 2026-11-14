module

public import Oberwolfach.OrdinaryExceptionalRimDegree
public import Oberwolfach.PhysicalRestrictedLocalScale

@[expose] public section
/-! The local degree of a sampled physical colour is its neighbour count
inside the protected vertex set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_local_state_degree
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (Inner:Finset V) (a:Fin 6) (x:V) (hx:x∈Inner):
    (spanningRestriction (longPhysicalStateGraph P σ {a}) Inner).degree x=
      ((P.neighborFinset x∩Inner).filter (fun y=>(σ (Sum.inl s(x,y))).1=a)).card :=by
  rw [←SimpleGraph.card_neighborFinset_eq_degree]
  congr 1
  ext y
  simp only [SimpleGraph.mem_neighborFinset,Finset.mem_filter,Finset.mem_inter]
  rw [spanningRestriction_adj]
  change (P.Adj x y ∧ (σ (Sum.inl s(x,y))).1∈({a}:Finset (Fin 6))) ∧ x∈Inner ∧ y∈Inner ↔
    (P.Adj x y ∧ y∈Inner) ∧ (σ (Sum.inl s(x,y))).1=a
  simp [hx,Finset.mem_singleton, and_left_comm, and_assoc]
  tauto

theorem ordinary_restricted_sup_degree_le
    {V:Type} [Fintype V] [DecidableEq V] (G H:SimpleGraph V) (Inner:Finset V) (v:V):
    (spanningRestriction (G⊔H) Inner).degree v≤
      (spanningRestriction G Inner).degree v+(spanningRestriction H Inner).degree v :=by
  have hsub:spanningRestriction (G⊔H) Inner≤spanningRestriction G Inner⊔spanningRestriction H Inner:=by
    intro x y h
    have hh:=(spanningRestriction_adj (G⊔H) Inner x y).mp h
    rcases hh.1 with hg|hh'
    · exact Or.inl ((spanningRestriction_adj G Inner x y).mpr ⟨hg,hh.2.1,hh.2.2⟩)
    · exact Or.inr ((spanningRestriction_adj H Inner x y).mpr ⟨hh',hh.2.1,hh.2.2⟩)
  have h1:=SimpleGraph.degree_le_of_le hsub (v:=v)
  have h2:=graph_degree_sup_le (spanningRestriction G Inner) (spanningRestriction H Inner) v
  have h2':(spanningRestriction G Inner⊔spanningRestriction H Inner).degree v≤
      (spanningRestriction G Inner).degree v+(spanningRestriction H Inner).degree v:=by
    convert h2 using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  exact h1.trans h2'
end Oberwolfach
