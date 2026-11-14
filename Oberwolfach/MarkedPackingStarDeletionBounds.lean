module

public import Oberwolfach.MarkedHubRowStarAvoidance
public import Oberwolfach.MarkedFiniteDeletionDegrees

@[expose] public section

/-! Avoiding an inner star gives zero deletion into its vertex domains
for every ambient root, not merely for roots in the induced subgraph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
  {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {m b:ℕ} {H₀ HK:V→U→Prop}

theorem marked_packing_star_avoidance_neighbours
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK)) (I:Finset V) (J:Finset U)
    (hstar:(M.biUnion markedWheelPhysicalResources).filter (markedStarResource I J)=∅):
    (∀ x,(markedPackingRimGraph M).neighborFinset x∩I=∅) ∧
    (∀ x,(Finset.univ.filter (markedPackingSpokes M x))∩J=∅) ∧
    (∀ u,(Finset.univ.filter (fun x=>markedPackingSpokes M x u))∩I=∅) ∧
    (∀ x∈I,∀ u,¬markedPackingSpokes M x u) ∧
    (∀ u∈J,∀ x,¬markedPackingSpokes M x u):=by
  have hnot (e:Finset V⊕(V×U)) (he:e∈M.biUnion markedWheelPhysicalResources):¬markedStarResource I J e:=by
    intro hs
    have hh:=Finset.mem_filter.mpr ⟨he,hs⟩
    rw [hstar] at hh
    exact Finset.notMem_empty e hh
  have hs (x:V) (u:U) (hxu:markedPackingSpokes M x u):x∉I∧u∉J:=by
    have hn:=hnot (Sum.inr (x,u)) ((markedPackingResources_spoke M x u).mpr hxu)
    exact ⟨fun hx=>hn (Or.inl hx),fun hu=>hn (Or.inr hu)⟩
  refine ⟨?_,?_,?_,fun x hx u hxu=>(hs x u hxu).1 hx,fun u hu x hxu=>(hs x u hxu).2 hu⟩
  · intro x
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro y hy
    have he:({x,y}:Finset V)∈markedPackingRims M:=
      (((markedPackingRimGraph M).mem_neighborFinset x y).mp (Finset.mem_inter.mp hy).1).2
    exact hnot (Sum.inl {x,y}) ((markedPackingResources_rim M _).mpr he)
      ⟨y,by simp,(Finset.mem_inter.mp hy).2⟩
  · intro x
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    exact (hs x u (Finset.mem_filter.mp (Finset.mem_inter.mp hu).1).2).2 (Finset.mem_inter.mp hu).2
  · intro u
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact (hs x u (Finset.mem_filter.mp (Finset.mem_inter.mp hx).1).2).1 (Finset.mem_inter.mp hx).2

theorem marked_packing_star_avoidance_rim_degree_zero
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK)) (I:Finset V) (J:Finset U)
    (hstar:(M.biUnion markedWheelPhysicalResources).filter (markedStarResource I J)=∅)
    (x:V) (hx:x∈I):(markedPackingRimGraph M).degree x=0:=by
  rw [←SimpleGraph.card_neighborFinset_eq_degree,Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro y hy
  have hxy:=((markedPackingRimGraph M).mem_neighborFinset x y).mp hy
  have hm:x∈(markedPackingRimGraph M).neighborFinset y∩I:=
    Finset.mem_inter.mpr ⟨((markedPackingRimGraph M).mem_neighborFinset y x).mpr hxy.symm,hx⟩
  rw [(marked_packing_star_avoidance_neighbours M I J hstar).1 y] at hm
  exact Finset.notMem_empty x hm

end Oberwolfach
