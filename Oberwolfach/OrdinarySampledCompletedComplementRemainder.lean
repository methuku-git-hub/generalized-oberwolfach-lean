module

public import Oberwolfach.OrdinaryCompletedActualComplementRemainder
public import Oberwolfach.LongPreparationPhysicalStates

@[expose] public section
/-! The completed complementary factors leave a subgraph of the original
sample, agreeing with its conflict-trimmed reference on the inner set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_sampled_completed_complement_remainder {n q:ℕ}
    (F:Fin q→SimpleGraph (Fin n)) (C:∀u,Finset (F u).ConnectedComponent)
    (f:∀u,{x:Fin n // (F u).connectedComponentMk x∉C u}↪Fin n)
    (Old New:Fin q→Finset (Sym2 (Fin n))) (P Fbad Target Protect:SimpleGraph (Fin n))
    (Inner:Finset (Fin n))
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e):
    let Sample:=longPhysicalStateGraph P σ {0,1,2,3,4}
    let Reference:=longPhysicalStateGraph P σ {0}\Fbad;
    Protect≤Reference → spanningRestriction Reference Inner≤Protect →
    (∀v∈Inner,∀w∈Inner,Target.Adj v w↔Sample.Adj v w) →
    (∀u x y,((F u).induce {x | (F u).connectedComponentMk x∉C u}).Adj x y→
      (Target\Protect).Adj (f u x) (f u y)) →
    (∀u,(((F u).induce {x | (F u).connectedComponentMk x∉C u}).edgeFinset).image (Sym2.map (f u))=Old u∪New u) →
    (∀e∈(ordinaryPostmatchingRequired Target Sample Reference Fbad (prescribedPhysicalUnion Old) Inner).edgeFinset,
      ∃u,e∈New u) →
    let Rem:=Target\ordinaryEmbeddedComplements F C f;
    Rem≤Sample ∧ Disjoint Rem Fbad ∧
      (∀v∈Inner,∀w∈Inner,Rem.Adj v w↔Reference.Adj v w) :=by
  intro Sample Reference hProtect hInner hTarget hAdj hSplit hCover Rem
  have hRef:Reference≤Sample:=by
    intro x y h
    change (P.Adj x y ∧ (σ (Sum.inl s(x,y))).1∈({0}:Finset (Fin 6))) ∧ ¬Fbad.Adj x y at h
    change P.Adj x y ∧ (σ (Sum.inl s(x,y))).1∈({0,1,2,3,4}:Finset (Fin 6))
    refine ⟨h.1.1,?_⟩
    have hc:(σ (Sum.inl s(x,y))).1=0:=by simpa using h.1.2
    simp [hc]
  have hBad:Disjoint Reference Fbad:=by
    apply disjoint_iff_inf_le.mpr
    intro x y h
    exact (h.1.2 h.2).elim
  exact ordinary_completed_actual_complement_remainder F C f Old New Target Sample Reference Protect Fbad Inner
    hRef hProtect hBad hInner hTarget hAdj hSplit hCover
end Oberwolfach
