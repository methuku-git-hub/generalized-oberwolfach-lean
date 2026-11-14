module

public import Oberwolfach.LongMarkedRimFromComplementArcSplit
public import Oberwolfach.MarkedPartitionedResidualHost

@[expose] public section
/-! Both parts of the corrected residual partition avoid the complements of
 the same packed factors. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance dualResidualOrdinaryFintype {V:Type} [Fintype V] (P:V×V→Prop)
    (T:Finset {a:V×V // P a}):Fintype (residualOrdinaryArc P T):=by
  unfold residualOrdinaryArc
  exact Fintype.ofFinite _
local instance dualResidualMarkedFintype {V:Type} [Fintype V] (P:V×V→Prop)
    (T:Finset {a:V×V // P a}):Fintype (residualMarkedArc P T):=by
  unfold residualMarkedArc
  exact Fintype.ofFinite _

theorem long_dual_residual_rim_avoids_complement
    {U V:Type} [Fintype U] [DecidableEq U] [Fintype V] [LinearOrder V] [Nonempty V]
    {X:U→Type} [∀u,Fintype (X u)] [∀u,DecidableEq (X u)]
    (F:∀u,SimpleGraph (X u)) (f:∀u,X u→V)
    (arcs:U→Finset (V×V)) (A:Finset (V×V)) (Small:SimpleGraph V)
    (hA:A=Finset.univ.biUnion arcs)
    (hSmall:Small.edgeFinset=A.image (fun a=>s(a.1,a.2)))
    (hExact:∀u,((F u).edgeFinset.image (Sym2.map (f u)))=
      (arcs u).image (fun a=>s(a.1,a.2)))
    (M:V→V→ℕ) (π:Equiv.Perm V)
    (T:Finset {a:V×V // longEligibleResidualArc M Small ⊥ a}):
    ∀u x y,(F u).Adj x y→
      ({f u x,f u y}:Finset V)∉markedPhysicalRimSet
        (fun x:residualOrdinaryArc (longEligibleResidualArc M Small ⊥) T=>x.val.val.1)
        (fun x:residualOrdinaryArc (longEligibleResidualArc M Small ⊥) T=>x.val.val.2)
        (fun x:residualMarkedArc (longEligibleResidualArc M Small ⊥) T=>x.val.val.1)
        (fun x:residualMarkedArc (longEligibleResidualArc M Small ⊥) T=>π.symm x.val.val.2) π:=by
  apply long_marked_rim_from_complement_arc_split F f arcs A Small hA hSmall hExact M _ _ _ _ π
  · intro e
    exact e.val.property
  · intro e
    simpa only [Equiv.apply_symm_apply] using e.val.property
end Oberwolfach
