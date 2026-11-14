module

public import Oberwolfach.RowCoverPackings
public import Oberwolfach.OrdinaryWheelRemainders

@[expose] public section

/-! Exact unions and deletion remainders for the successive row covers. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {Q F:SimpleGraph V} {H:V→U→Prop} {r n K:ℕ}

theorem ordinaryPacking_resources (M:Finset (OrdinaryWheel Q F H r)) :
    M.biUnion ordinaryWheelResources=ordinaryHostResources (ordinaryWheelRimGraph M) (ordinaryPackingSpokes M) := by
  ext e
  cases e with
  | inl e =>
    simp only [Finset.mem_biUnion,ordinaryWheelResources_rim,ordinaryHostResources_rim]
    exact (ordinaryWheelRimGraph_edges M e).symm
  | inr vu =>
    rw [ordinaryHostResources_spoke]
    exact (ordinaryPackingSpokes_iff M vu.1 vu.2).symm

theorem ordinaryPacking_decomposition (M:Finset (OrdinaryWheel Q F H r))
    (hM:∀ W∈M,∀ Z∈M,W≠Z → Disjoint (ordinaryWheelResources W) (ordinaryWheelResources Z)) :
    HasOrdinaryWheelDecomposition (ordinaryWheelRimGraph M) (ordinaryPackingSpokes M) r :=
  ordinary_packing_exact_decomposition M hM (ordinaryPacking_resources M)

theorem row_cover_union_packing (C:Fin n→Finset (OrdinaryWheel Q F H r))
    (x:Fin n→V) (A:Finset V)
    (hc:∀ i,OrdinaryRowCover (C i) (x i) A K)
    (hcross:∀ i j,i≠j → Disjoint ((C i).biUnion ordinaryWheelResources) ((C j).biUnion ordinaryWheelResources)) :
    let M:=Finset.univ.biUnion C
    (∀ W∈M,∀ Z∈M,W≠Z → Disjoint (ordinaryWheelResources W) (ordinaryWheelResources Z)) ∧
    HasOrdinaryWheelDecomposition (ordinaryWheelRimGraph M) (ordinaryPackingSpokes M) r ∧
    (∀ i a,(ordinaryWheelRimGraph M).Adj (x i) a ↔ Q.Adj (x i) a) ∧
    (∀ i u,ordinaryPackingSpokes M (x i) u ↔ H (x i) u) := by
  dsimp only
  let M:=Finset.univ.biUnion C
  have hp:∀ W∈M,∀ Z∈M,W≠Z → Disjoint (ordinaryWheelResources W) (ordinaryWheelResources Z):=by
    intro W hW Z hZ hne
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hW
    obtain ⟨j,_,hj⟩:=Finset.mem_biUnion.mp hZ
    by_cases he:i=j
    · subst j;exact (hc i).disjoint W hi Z hj hne
    · exact (hcross i j he).mono (resource_subset_union ordinaryWheelResources (C i) W hi)
        (resource_subset_union ordinaryWheelResources (C j) Z hj)
  refine ⟨hp,ordinaryPacking_decomposition M hp,?_,?_⟩
  · intro i a
    constructor
    · intro ha;exact ordinaryWheelRimGraph_subhost M ha
    · intro ha
      have hci:=(hc i).rims a
      rw [ordinaryWheelRimGraph_biUnion]
      exact SimpleGraph.iSup_adj.mpr ⟨i,hci.mpr ha⟩
  · intro i u
    constructor
    · rintro ⟨W,hW,hhub,hv⟩
      rw [←hhub];exact W.property.1 (x i) hv
    · intro hu
      exact (ordinaryPackingSpokes_biUnion C (x i) u).mpr ⟨i,((hc i).spokes u).mpr hu⟩

theorem row_cover_union_degree_bounds (C:Fin n→Finset (OrdinaryWheel Q F H r))
    (x:Fin n→V) (A:Finset V) (hxA:∀ i,x i∉A) (hc:∀ i,OrdinaryRowCover (C i) (x i) A K) :
    let M:=Finset.univ.biUnion C
    (∀ a∈A,(ordinaryWheelRimGraph M).degree a≤n*(2*(K+1))) ∧
    (∀ a∈A,(Finset.univ.filter (ordinaryPackingSpokes M a)).card≤n*(K+1)) ∧
    (∀ u,(Finset.univ.filter (fun a=>ordinaryPackingSpokes M a u)).card≤n*r) := by
  dsimp only
  constructor
  · intro a ha
    have hd (i:Fin n):(ordinaryWheelRimGraph (C i)).degree a≤2*(K+1):=
      (hc i).rimDegree a (fun he=>hxA i (he ▸ ha))
    have hh:=graph_iSup_local_degree_bound (fun i=>ordinaryWheelRimGraph (C i)) Finset.univ a (2*(K+1)) hd
    simp only [Finset.inter_univ,SimpleGraph.card_neighborFinset_eq_degree] at hh
    have hcard:(Finset.univ.filter (fun i:Fin n=>∃ b∈(Finset.univ:Finset V),(ordinaryWheelRimGraph (C i)).Adj a b)).card≤n:=by
      exact (Finset.card_filter_le _ _).trans (by simp)
    have hh':(⨆ i,ordinaryWheelRimGraph (C i)).degree a≤n*(2*(K+1)):=
      hh.trans (by simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (2*(K+1)) hcard)
    convert hh' using 1;rw [ordinaryWheelRimGraph_biUnion]
  constructor
  · intro a ha
    have hh:=relation_iUnion_degree_bound (fun i=>ordinaryPackingSpokes (C i) a) (K+1)
      (fun i=>(hc i).rowDegree a (fun he=>hxA i (he ▸ ha)))
    simpa only [Fintype.card_fin,←ordinaryPackingSpokes_biUnion] using hh
  · intro u
    have hh:=relation_iUnion_degree_bound (fun i a=>ordinaryPackingSpokes (C i) a u) r (fun i=>(hc i).columnDegree u)
    simpa only [Fintype.card_fin,←ordinaryPackingSpokes_biUnion] using hh

theorem row_cover_remainder (C:Fin n→Finset (OrdinaryWheel Q F H r))
    (x:Fin n→V) (A:Finset V)
    (hc:∀ i,OrdinaryRowCover (C i) (x i) A K)
    (hcross:∀ i j,i≠j → Disjoint ((C i).biUnion ordinaryWheelResources) ((C j).biUnion ordinaryWheelResources))
    (hQ:∀ v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hU:∀ u,r∣(Finset.univ.filter (fun v=>H v u)).card) :
    let M:=Finset.univ.biUnion C
    (∀ v,(Q\ordinaryWheelRimGraph M).degree v=2*(Finset.univ.filter (fun u=>H v u∧¬ordinaryPackingSpokes M v u)).card) ∧
    (∀ u,r∣(Finset.univ.filter (fun v=>H v u∧¬ordinaryPackingSpokes M v u)).card) ∧
    (∀ i a,¬(Q\ordinaryWheelRimGraph M).Adj (x i) a) ∧
    (∀ i u,¬(H (x i) u∧¬ordinaryPackingSpokes M (x i) u)) := by
  dsimp only
  let M:=Finset.univ.biUnion C
  have hh:=row_cover_union_packing C x A hc hcross
  have hsp:∀ v u,ordinaryPackingSpokes M v u → H v u:=by
    rintro v u ⟨W,hW,hh,hv⟩;rw [←hh];exact W.property.1 v hv
  have hbal:=ordinary_decomposition_remainder_balance Q (ordinaryWheelRimGraph M) H (ordinaryPackingSpokes M)
    r (ordinaryWheelRimGraph_subhost M) hsp hQ hU hh.2.1
  refine ⟨hbal.1,hbal.2,?_,?_⟩
  · intro i a ha;exact ha.2 ((hh.2.2.1 i a).mpr ha.1)
  · intro i u hu;exact hu.2 ((hh.2.2.2 i u).mpr hu.1)

end Oberwolfach
