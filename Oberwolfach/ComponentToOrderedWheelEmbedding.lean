module

public import Oberwolfach.RegularCycleIsomorphism
public import Oberwolfach.OrderedOrdinaryWheelResources
public import Oberwolfach.AlternatingCycle

@[expose] public section
/-! A prescribed cycle component of the correct order maps into the
selected ordered wheel, using exactly its rim vertices and spokes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n r:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem component_to_ordered_ordinary_wheel_embedding
    (F:SimpleGraph (Fin n)) (hF:F.IsRegularOfDegree 2) (C:F.ConnectedComponent)
    (π:Equiv.Perm (Fin n)) (b:ℕ) (W:OrderedOrdinaryWheel (U:=U) π b r)
    (hsize:Fintype.card C=r):
    ∃ f:C↪Fin n,
      (∀x,∃i:Fin r,f x=W.1.val i) ∧
      (∀i:Fin r,∃x:C,f x=W.1.val i) ∧
      (∀x y,C.toSimpleGraph.Adj x y →
        ∃i:Fin r,(f x=W.1.val i ∧ f y=W.1.val (cycleNext i)) ∨
          (f y=W.1.val i ∧ f x=W.1.val (cycleNext i))) ∧
      (∀x,Sum.inr (f x,W.2)∈orderedOrdinaryResources W) :=by
  have hthree:3≤r:=by rw [←hsize];exact (component_regular_two_cycle_iso F hF C).1
  obtain ⟨e0⟩:Nonempty (SimpleGraph.cycleGraph r ≃g C.toSimpleGraph):=by
    rw [←hsize]
    exact (component_regular_two_cycle_iso F hF C).2
  let f:C↪Fin n:=⟨fun x=>W.1.val (e0.symm x),by
    intro x y he
    apply e0.symm.injective
    exact (permutationSeparated_injective π b W.1.val W.1.property) he⟩
  refine ⟨f,?_,?_,?_,?_⟩
  · intro x
    exact ⟨e0.symm x,rfl⟩
  · intro i
    refine ⟨e0 i,?_⟩
    simp [f]
  · intro x y hxy
    have hc:(SimpleGraph.cycleGraph r).Adj (e0.symm x) (e0.symm y):=e0.symm.map_rel_iff.mpr hxy
    rcases (cycleGraph_adj_next (by omega) _ _).mp hc with h|h
    · refine ⟨e0.symm x,Or.inl ⟨rfl,?_⟩⟩
      change W.1.val (e0.symm y)=W.1.val (cycleNext (e0.symm x))
      rw [h]
    · refine ⟨e0.symm y,Or.inr ⟨rfl,?_⟩⟩
      change W.1.val (e0.symm x)=W.1.val (cycleNext (e0.symm y))
      rw [h]
  · intro x
    apply (orderedOrdinaryResources_spoke W _).mpr
    exact ⟨e0.symm x,rfl⟩
end Oberwolfach
