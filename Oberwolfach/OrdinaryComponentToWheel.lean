module

public import Oberwolfach.RegularCycleIsomorphism
public import Oberwolfach.OrdinaryDecompositionHubCycleCounts
public import Oberwolfach.OrdinaryTransferCycles

@[expose] public section
/-! A reserved component of a prescribed two-factor embeds isomorphically
onto any wheel rim of the same length. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_component_to_wheel {n r:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (F:SimpleGraph (Fin n)) (hF:F.IsRegularOfDegree 2) (C:F.ConnectedComponent)
    (hC:Fintype.card C=r) (W:UniversalOrdinaryWheel (Fin n) U r):
    ∃f:C↪Fin n, Set.range f=(ordinaryWheelRim W).support ∧
      ∀x y:C,C.toSimpleGraph.Adj x y↔(ordinaryWheelRim W).Adj (f x) (f y) :=by
  have hR:IsEmbeddedCycle (ordinaryWheelRim W) r:=W.val.1.val.property
  obtain ⟨hr,g,hg⟩:=hR
  obtain ⟨e⟩:Nonempty (SimpleGraph.cycleGraph r ≃g C.toSimpleGraph):=by
    rw [←hC]
    exact (component_regular_two_cycle_iso F hF C).2
  let f:C↪Fin n:=e.symm.toEquiv.toEmbedding.trans g
  refine ⟨f,?_,?_⟩
  · rw [hg,cycle_map_support hr]
    ext x
    constructor
    · rintro ⟨v,rfl⟩
      exact ⟨e.symm v,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨e i,by simp [f]⟩
  · intro x y
    rw [hg]
    change C.toSimpleGraph.Adj x y↔((SimpleGraph.cycleGraph r).map g).Adj (g (e.symm x)) (g (e.symm y))
    rw [SimpleGraph.map_adj_apply]
    exact e.symm.map_rel_iff.symm
end Oberwolfach
