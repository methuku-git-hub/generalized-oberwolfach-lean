module

public import Oberwolfach.FactorComponentEnumeration

@[expose] public section
/-! Enumerate all components of an actual two-factor at once. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem two_factor_all_components_enumerated (F:SimpleGraph V)
    (hF:F.IsRegularOfDegree 2):
    ∃ (root:F.ConnectedComponent→V) (tail:F.ConnectedComponent→List V),
      (∀ c,(root c::tail c).Nodup ∧ 3≤(root c::tail c).length) ∧
      (∀ c x,x∈root c::tail c ↔ x∈c.supp) ∧
      (∀ c c' x,x∈root c::tail c→x∈root c'::tail c'→c=c') ∧
      (∀ x,∃ c,x∈root c::tail c) ∧
      (∀ x y,F.Adj x y ↔ ∃ c,x∈root c::tail c ∧
        s(x,y)∈prescribedOrderedPathEdges ((root c::tail c)++[root c])) := by
  choose root tail hnd hlen hvertices hedges using
    fun c : F.ConnectedComponent => two_factor_component_enumeration F hF c
  refine ⟨root,tail,?_,hvertices,?_,?_,?_⟩
  · intro c
    exact ⟨hnd c,hlen c⟩
  · intro c c' x hx hx'
    have ha:= (hvertices c x).1 hx
    have hb:= (hvertices c' x).1 hx'
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at ha hb
    exact ha.symm.trans hb
  · intro x
    refine ⟨F.connectedComponentMk x, (hvertices _ _).2 ?_⟩
    rfl
  · intro x y
    constructor
    · intro h
      let c:=F.connectedComponentMk x
      have hx:x∈root c::tail c := (hvertices c x).2 rfl
      exact ⟨c,hx,(hedges c x hx y).1 h⟩
    · rintro ⟨c,hx,he⟩
      exact (hedges c x hx y).2 he
end Oberwolfach
