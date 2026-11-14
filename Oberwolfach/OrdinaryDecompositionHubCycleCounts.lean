module

public import Oberwolfach.OrdinaryDecompositionHubCycles

@[expose] public section
/-! The wheels at a hub form a disjoint cycle factor of its spoke set,
with the exact number of cycles required by the ordinary reservation. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_decomposition_hub_cycle_counts {V U:Type} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U]
    (Q:SimpleGraph V) (H:V→U→Prop) (r:ℕ)
    (hdec:HasOrdinaryWheelDecomposition Q H r):
    ∃M:Finset (UniversalOrdinaryWheel V U r),
      (∀W∈M,IsEmbeddedCycle (ordinaryWheelRim W) r) ∧
      (∀W∈M,∀Z∈M,W≠Z→Disjoint (ordinaryWheelResources W) (ordinaryWheelResources Z)) ∧
      (∀u,(Finset.univ.filter (fun v=>H v u))=
        (M.filter (fun W=>ordinaryWheelHub W=u)).biUnion (fun W=>(ordinaryWheelRim W).support.toFinset)) ∧
      (∀u,r*(M.filter (fun W=>ordinaryWheelHub W=u)).card=(Finset.univ.filter (fun v=>H v u)).card) ∧
      (∀W∈M,∀Z∈M,W≠Z→ ordinaryWheelHub W=ordinaryWheelHub Z→
        Disjoint (ordinaryWheelRim W).support.toFinset (ordinaryWheelRim Z).support.toFinset) :=by
  obtain ⟨M,hcycle,hspoke,hdis,hspokeDis,hRim⟩:=ordinary_decomposition_hub_cycles Q H r hdec
  refine ⟨M,hcycle,hdis,?_,?_,hspokeDis⟩
  · intro u
    ext v
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_biUnion,Set.mem_toFinset]
    constructor
    · intro hv
      obtain ⟨W,hW,_⟩:=(hspoke u v).1 hv
      exact ⟨W,⟨hW.1,hW.2.1⟩,hW.2.2⟩
    · rintro ⟨W,⟨hW,hu⟩,hv⟩
      apply (hspoke u v).2
      refine ⟨W,⟨hW,hu,hv⟩,?_⟩
      intro Z hZ
      by_contra hZW
      have hWv:v∈(ordinaryWheelRim W).support.toFinset:=by simpa using hv
      have hZv:v∈(ordinaryWheelRim Z).support.toFinset:=by simpa using hZ.2.2
      exact Finset.disjoint_left.mp (hspokeDis Z hZ.1 W hW hZW (hZ.2.1.trans hu.symm)) hZv hWv
  · intro u
    let Mu:=M.filter (fun W=>ordinaryWheelHub W=u)
    have hcover:(Finset.univ.filter (fun v=>H v u))=Mu.biUnion (fun W=>(ordinaryWheelRim W).support.toFinset):=by
      ext v
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_biUnion,Set.mem_toFinset,Mu]
      constructor
      · intro hv
        obtain ⟨W,hW,_⟩:=(hspoke u v).1 hv
        exact ⟨W,⟨hW.1,hW.2.1⟩,hW.2.2⟩
      · rintro ⟨W,⟨hW,hu⟩,hv⟩
        apply (hspoke u v).2
        refine ⟨W,⟨hW,hu,hv⟩,?_⟩
        intro Z hZ
        by_contra hZW
        have hWv:v∈(ordinaryWheelRim W).support.toFinset:=by simpa using hv
        have hZv:v∈(ordinaryWheelRim Z).support.toFinset:=by simpa using hZ.2.2
        exact Finset.disjoint_left.mp (hspokeDis Z hZ.1 W hW hZW (hZ.2.1.trans hu.symm)) hZv hWv
    have hd:(Mu:Set (UniversalOrdinaryWheel V U r)).PairwiseDisjoint
        (fun W=>(ordinaryWheelRim W).support.toFinset):=by
      intro W hW Z hZ hWZ
      have hw:W∈M ∧ ordinaryWheelHub W=u:=Finset.mem_filter.mp hW
      have hz:Z∈M ∧ ordinaryWheelHub Z=u:=Finset.mem_filter.mp hZ
      exact hspokeDis W hw.1 Z hz.1 hWZ (hw.2.trans hz.2.symm)
    rw [hcover,Finset.card_biUnion hd]
    have he:∀W∈Mu,(ordinaryWheelRim W).support.toFinset.card=r:=by
      intro W hW
      exact (hcycle W (Finset.mem_filter.mp hW).1).support_card
    rw [Finset.sum_const_nat he]
    exact Nat.mul_comm _ _
end Oberwolfach
