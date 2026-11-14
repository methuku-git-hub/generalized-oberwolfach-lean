module

public import Oberwolfach.OrdinaryDecompositionHubCycleCounts

@[expose] public section
/-! Match each reserved source component to a distinct wheel at its own hub,
using the exact spoke count from the ordinary completion. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_reserved_wheel_matching {n r:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (Q:SimpleGraph (Fin n)) (H:Fin n→U→Prop) (hr:0<r)
    (hdec:HasOrdinaryWheelDecomposition Q H r)
    (F:U→SimpleGraph (Fin n)) (C:∀u,Finset (F u).ConnectedComponent)
    (hspokes:∀u,(Finset.univ.filter (fun v=>H v u)).card=r*(C u).card):
    ∃M:Finset (UniversalOrdinaryWheel (Fin n) U r),
    ∃W:∀u,↥(C u)→UniversalOrdinaryWheel (Fin n) U r,
      (∀u,Function.Injective (W u)) ∧
      (∀u c,W u c∈M ∧ ordinaryWheelHub (W u c)=u ∧ ordinaryWheelRim (W u c)≤Q) ∧
      (∀u c v,v∈(ordinaryWheelRim (W u c)).support→H v u) ∧
      (∀u v (c:↥(C u)) (d:↥(C v)),u≠v→
        Disjoint (ordinaryWheelResources (W u c)) (ordinaryWheelResources (W v d))) ∧
      (∀u (c d:↥(C u)),c≠d→Disjoint (ordinaryWheelRim (W u c)).support.toFinset
        (ordinaryWheelRim (W u d)).support.toFinset) :=by
  obtain ⟨M,hcycle,hspoke,hdis,hspokeDis,hRim⟩:=ordinary_decomposition_hub_cycles Q H r hdec
  have hcounts:∀u,r*(M.filter (fun W=>ordinaryWheelHub W=u)).card=(Finset.univ.filter (fun v=>H v u)).card:=by
    intro u
    have hcover:(Finset.univ.filter (fun v=>H v u))=
        (M.filter (fun W=>ordinaryWheelHub W=u)).biUnion (fun W=>(ordinaryWheelRim W).support.toFinset):=by
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
        have hz:v∈(ordinaryWheelRim Z).support.toFinset:=by simpa using hZ.2.2
        have hw:v∈(ordinaryWheelRim W).support.toFinset:=by simpa using hv
        exact Finset.disjoint_left.mp (hspokeDis Z hZ.1 W hW hZW (hZ.2.1.trans hu.symm)) hz hw
    have hpair:(↑(M.filter (fun W=>ordinaryWheelHub W=u)):Set (UniversalOrdinaryWheel (Fin n) U r)).PairwiseDisjoint
        (fun W=>(ordinaryWheelRim W).support.toFinset):=by
      intro W hW Z hZ hWZ
      have hw:=Finset.mem_filter.mp hW
      have hz:=Finset.mem_filter.mp hZ
      exact hspokeDis W hw.1 Z hz.1 hWZ (hw.2.trans hz.2.symm)
    rw [hcover,Finset.card_biUnion hpair]
    have hh:∀W∈M.filter (fun W=>ordinaryWheelHub W=u),
        (ordinaryWheelRim W).support.toFinset.card=r:=fun W hW=>(hcycle W (Finset.mem_filter.mp hW).1).support_card
    rw [Finset.sum_const_nat hh]
    exact Nat.mul_comm _ _
  have hcard:∀u,(C u).card=(M.filter (fun W=>ordinaryWheelHub W=u)).card:=by
    intro u
    exact (Nat.mul_left_cancel hr ((hspokes u).symm.trans (hcounts u).symm))
  let e:∀u,↥(C u)≃↥(M.filter (fun W=>ordinaryWheelHub W=u)):=fun u=>
    Fintype.equivOfCardEq (by simpa only [Fintype.card_coe] using hcard u)
  let W:∀u,↥(C u)→UniversalOrdinaryWheel (Fin n) U r:=fun u c=>(e u c).val
  have hWin:∀u c,W u c∈M ∧ ordinaryWheelHub (W u c)=u:=by
    intro u c
    exact Finset.mem_filter.mp (e u c).property
  have hWInQ:∀u c,ordinaryWheelRim (W u c)≤Q:=by
    intro u c x y hxy
    apply (hRim x y).2
    refine ⟨W u c,⟨(hWin u c).1,hxy⟩,?_⟩
    intro Z hZ
    by_contra hZW
    have hz:Sum.inl s(x,y)∈ordinaryWheelResources Z:=(ordinaryWheelResources_rim Z s(x,y)).2 hZ.2
    have hw:Sum.inl s(x,y)∈ordinaryWheelResources (W u c):=(ordinaryWheelResources_rim (W u c) s(x,y)).2 hxy
    exact Finset.disjoint_left.mp (hdis Z hZ.1 (W u c) (hWin u c).1 hZW) hz hw
  refine ⟨M,W,?_,?_,?_,?_,?_⟩
  · intro u c d heq
    apply (e u).injective
    exact Subtype.ext heq
  · intro u c
    exact ⟨(hWin u c).1,(hWin u c).2,hWInQ u c⟩
  · intro u c v hv
    apply (hspoke u v).2
    refine ⟨W u c,⟨(hWin u c).1,(hWin u c).2,hv⟩,?_⟩
    intro Z hZ
    by_contra hZW
    have hz:Sum.inr (v,u)∈ordinaryWheelResources Z:=(ordinaryWheelResources_spoke Z v u).2 hZ.2
    have hw:Sum.inr (v,u)∈ordinaryWheelResources (W u c):=(ordinaryWheelResources_spoke (W u c) v u).2 ⟨(hWin u c).2,hv⟩
    exact Finset.disjoint_left.mp (hdis Z hZ.1 (W u c) (hWin u c).1 hZW) hz hw
  · intro u v c d huv
    apply hdis (W u c) (hWin u c).1 (W v d) (hWin v d).1
    intro heq
    apply huv
    exact ((hWin u c).2.symm.trans (congrArg ordinaryWheelHub heq)).trans (hWin v d).2
  · intro u c d hcd
    apply hspokeDis (W u c) (hWin u c).1 (W u d) (hWin u d).1
    · intro heq
      apply hcd
      apply (e u).injective
      exact Subtype.ext heq
    · exact (hWin u c).2.trans (hWin u d).2.symm
end Oberwolfach
