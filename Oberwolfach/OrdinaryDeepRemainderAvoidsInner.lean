module

public import Oberwolfach.OrdinaryPackingGlue
public import Oberwolfach.OrdinaryDeepCoverNamedEvent

@[expose] public section
/-! A deep packing in the prescribed remainder adds no inner resource when
    all original root-incident inner resources were prescribed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {Q F:SimpleGraph V} {H:V→U→Prop} {r:ℕ}

theorem ordinary_deep_remainder_avoids_inner
    (PE:Finset (OrdinaryWheel Q F H r))
    (M:Finset (OrdinaryWheel (Q\ordinaryWheelRimGraph PE) F (fun v u=>H v u∧¬ordinaryPackingSpokes PE v u) r))
    (I T:Finset V) (J:Finset U) (E:Finset (Sym2 V⊕(V×U)))
    (hPE:PE.biUnion ordinaryWheelResources∩ordinaryHostResources (spanningRestriction Q I)
      (fun v u=>H v u∧v∈I∧u∈J)=E)
    (hMavoidR:∀v∈I\T,∀w,¬(ordinaryWheelRimGraph M).Adj v w)
    (hMavoidS:∀v∈I\T,∀u,¬ordinaryPackingSpokes M v u)
    (hErim:∀v∈T,∀w∈I,Q.Adj v w→Sum.inl s(v,w)∈E)
    (hErow:∀v∈T,∀u∈J,H v u→Sum.inr (v,u)∈E) :
    Disjoint (M.biUnion ordinaryWheelResources)
      (ordinaryHostResources (spanningRestriction Q I) (fun v u=>H v u∧v∈I∧u∈J)) := by
  apply Finset.disjoint_left.mpr
  intro e he hi
  cases e with
  | inl e=>
    obtain ⟨Y,hY,hYres⟩:=Finset.mem_biUnion.mp he
    have hR:=(ordinaryWheelResources_rim Y e).mp hYres
    have hI:=(ordinaryHostResources_rim (spanningRestriction Q I) _ e).mp hi
    induction e using Sym2.ind with
    | _ v w=>
      have hvI:v∈I:=((spanningRestriction_adj Q I v w).mp hI).2.1
      have hwI:w∈I:=((spanningRestriction_adj Q I v w).mp hI).2.2
      have hM:(ordinaryWheelRimGraph M).Adj v w:=
        (ordinaryWheelRimGraph_edges M s(v,w)).mpr ⟨Y,hY,hR⟩
      have hRem:(Q\ordinaryWheelRimGraph PE).Adj v w:=ordinaryWheelRimGraph_subhost M hM
      have hvT:v∈T:=by
        by_contra hnot
        exact hMavoidR v (Finset.mem_sdiff.mpr ⟨hvI,hnot⟩) w hM
      have heE:Sum.inl s(v,w)∈E:=hErim v hvT w hwI hRem.1
      have hePE:Sum.inl s(v,w)∈PE.biUnion ordinaryWheelResources:=
        (Finset.mem_inter.mp (hPE ▸ heE)).1
      obtain ⟨Y',hY',hY'res⟩:=Finset.mem_biUnion.mp hePE
      have hPEedge:(ordinaryWheelRimGraph PE).Adj v w:=
        (ordinaryWheelRimGraph_edges PE s(v,w)).mpr ⟨Y',hY',(ordinaryWheelResources_rim Y' _).mp hY'res⟩
      exact hRem.2 hPEedge
  | inr vu=>
    rcases vu with ⟨v,u⟩
    obtain ⟨_,hvI,huJ⟩:=(ordinaryHostResources_spoke (spanningRestriction Q I) _ v u).mp hi
    have hM:ordinaryPackingSpokes M v u:=(ordinaryPackingSpokes_iff M v u).2 he
    obtain ⟨Y,hY,hHub,hV⟩:=hM
    have hRem:H v u∧¬ordinaryPackingSpokes PE v u:=by
      rw [←hHub]
      exact Y.property.1 v hV
    have hvT:v∈T:=by
      by_contra hnot
      exact hMavoidS v (Finset.mem_sdiff.mpr ⟨hvI,hnot⟩) u ⟨Y,hY,hHub,hV⟩
    have heE:Sum.inr (v,u)∈E:=hErow v hvT u huJ hRem.1
    have hePE:Sum.inr (v,u)∈PE.biUnion ordinaryWheelResources:=(Finset.mem_inter.mp (hPE ▸ heE)).1
    exact hRem.2 ((ordinaryPackingSpokes_iff PE v u).2 hePE)
end Oberwolfach
