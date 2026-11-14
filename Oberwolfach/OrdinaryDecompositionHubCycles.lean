module

public import Oberwolfach.OrdinaryExactDecomposition

@[expose] public section
/-! A wheel decomposition partitions the spokes at each hub into the
supports of uniquely determined, vertex-disjoint cycles. Rim edges are
likewise used once across all hubs. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_decomposition_hub_cycles {V U:Type} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U]
    (Q:SimpleGraph V) (H:V→U→Prop) (r:ℕ)
    (hdec:HasOrdinaryWheelDecomposition Q H r):
    ∃M:Finset (UniversalOrdinaryWheel V U r),
      (∀W∈M,IsEmbeddedCycle (ordinaryWheelRim W) r) ∧
      (∀u v,H v u↔∃!W:UniversalOrdinaryWheel V U r,
        W∈M ∧ ordinaryWheelHub W=u ∧ v∈(ordinaryWheelRim W).support) ∧
      (∀W∈M,∀Z∈M,W≠Z→Disjoint (ordinaryWheelResources W) (ordinaryWheelResources Z)) ∧
      (∀W∈M,∀Z∈M,W≠Z→ ordinaryWheelHub W=ordinaryWheelHub Z→
        Disjoint (ordinaryWheelRim W).support.toFinset (ordinaryWheelRim Z).support.toFinset) ∧
      (∀x y,Q.Adj x y↔∃!W:UniversalOrdinaryWheel V U r,
        W∈M ∧ (ordinaryWheelRim W).Adj x y) :=by
  obtain ⟨M,hdis,hcover⟩:=hdec
  refine ⟨M,?_,?_,hdis,?_,?_⟩
  · intro W hW
    exact W.val.1.val.property
  · intro u v
    constructor
    · intro h
      have he:Sum.inr (v,u)∈M.biUnion ordinaryWheelResources:=by
        rw [hcover,ordinaryHostResources_spoke]
        exact h
      obtain ⟨W,hW,hWu⟩:=Finset.mem_biUnion.mp he
      have hWu':ordinaryWheelHub W=u ∧ v∈(ordinaryWheelRim W).support:=
        (ordinaryWheelResources_spoke W v u).1 hWu
      refine ⟨W,⟨hW,hWu'⟩,?_⟩
      intro Z hZ
      by_contra hZW
      have hz:Sum.inr (v,u)∈ordinaryWheelResources Z:=
        (ordinaryWheelResources_spoke Z v u).2 hZ.2
      exact Finset.disjoint_left.mp (hdis Z hZ.1 W hW hZW) hz hWu
    · rintro ⟨W,⟨hW,hWu⟩,_⟩
      have he:Sum.inr (v,u)∈M.biUnion ordinaryWheelResources:=
        Finset.mem_biUnion.mpr ⟨W,hW,(ordinaryWheelResources_spoke W v u).2 hWu⟩
      rw [hcover,ordinaryHostResources_spoke] at he
      exact he
  · intro W hW Z hZ hWZ hHub
    apply Finset.disjoint_left.mpr
    intro v hvW hvZ
    have hvW':v∈(ordinaryWheelRim W).support:=by simpa using hvW
    have hvZ':v∈(ordinaryWheelRim Z).support:=by simpa using hvZ
    have heW:Sum.inr (v,ordinaryWheelHub W)∈ordinaryWheelResources W:=
      (ordinaryWheelResources_spoke W v _).2 ⟨rfl,hvW'⟩
    have heZ:Sum.inr (v,ordinaryWheelHub W)∈ordinaryWheelResources Z:=
      (ordinaryWheelResources_spoke Z v _).2 ⟨hHub.symm,hvZ'⟩
    exact Finset.disjoint_left.mp (hdis W hW Z hZ hWZ) heW heZ
  · intro x y
    constructor
    · intro h
      have he:Sum.inl s(x,y)∈M.biUnion ordinaryWheelResources:=by
        rw [hcover,ordinaryHostResources_rim]
        exact h
      obtain ⟨W,hW,hxy⟩:=Finset.mem_biUnion.mp he
      have hxy':(ordinaryWheelRim W).Adj x y:=(ordinaryWheelResources_rim W s(x,y)).1 hxy
      refine ⟨W,⟨hW,hxy'⟩,?_⟩
      intro Z hZ
      by_contra hZW
      have hz:Sum.inl s(x,y)∈ordinaryWheelResources Z:=
        (ordinaryWheelResources_rim Z s(x,y)).2 hZ.2
      exact Finset.disjoint_left.mp (hdis Z hZ.1 W hW hZW) hz hxy
    · rintro ⟨W,⟨hW,hxy⟩,_⟩
      have he:Sum.inl s(x,y)∈M.biUnion ordinaryWheelResources:=
        Finset.mem_biUnion.mpr ⟨W,hW,(ordinaryWheelResources_rim W s(x,y)).2 hxy⟩
      rw [hcover,ordinaryHostResources_rim] at he
      exact he
end Oberwolfach
