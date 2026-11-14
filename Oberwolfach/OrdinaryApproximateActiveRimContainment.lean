module

public import Oberwolfach.OrdinaryPhysicalMatchingRimResidual
public import Oberwolfach.OrdinaryShiftedActiveRimFiber
public import Oberwolfach.OrdinaryEligibleHost
public import Oberwolfach.LongPreparationPhysicalStates
public import Oberwolfach.RawMarkedRimDeletion
public import Oberwolfach.MarkedExpandedApproximateProjection

@[expose] public section
/-! Outside the bounded conflict and deletion graphs, every colour-2
physical edge is an active rim resource for the ordinary matching. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_approximate_colour_two_active_rim_containment
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P Del:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e):
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let raw':=rawMarkedDeleteRims raw Del.edgeFinset
    let Host:=ordinaryEligibleHost P π d
    let state:=typedMarkedResourceState (ordinaryShiftedPairRims Host π d raw') (rawMarkedPairSpokes π d raw' true true)
    let φ:=ordinaryMixedPhysicalResource (U:=U) π
    let ι:PhysicalSampledActive φ state↪Sym2 (Fin n)⊕(Fin n×U):=Function.Embedding.subtype _;
    longPhysicalStateGraph P σ {2}≤(physicalRimResidualGraph ι ∅⊔permutationConflictGraph π (3*d+2))⊔Del:=by
  intro raw raw' Host state φ ι x y hxy
  by_cases hd:Del.Adj x y
  · exact Or.inr hd
  by_cases hc:(permutationConflictGraph π (3*d+2)).Adj x y
  · exact Or.inl (Or.inr hc)
  have hP:P.Adj x y:=hxy.1
  have hfar:¬PermutationClose π (3*d+2) x y:=by
    intro hh
    exact hc ⟨hP.ne,hh⟩
  have hHost:Host.Adj x y:=(ordinary_eligible_host_adj P π d x y).mpr ⟨hP,hfar⟩
  have hcolour:(σ (Sum.inl s(x,y))).1=2:=by simpa using hxy.2
  have hbits:orientationBit x y=(σ (Sum.inl s(x,y))).2 ∨ orientationBit y x=(σ (Sum.inl s(x,y))).2:=by
    have hh:=orientationBit_ne_swap x y hP.ne
    cases hx:orientationBit x y <;> cases hy:orientationBit y x <;> cases hz:(σ (Sum.inl s(x,y))).2 <;> simp_all
  have hDel:s(x,y)∉Del.edgeFinset:=by
    intro he
    exact hd (SimpleGraph.mem_edgeFinset.mp he)
  have hactive:∃a,state a=true ∧ φ a=Sum.inl s(x,y):=by
    rcases hbits with hb|hb
    · let a:((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U):=Sum.inl (Sum.inl (x,y))
      have hraw:raw' (Sum.inl s(x,y))=some (false,orientationBit x y):=by
        simp [raw',raw,rawMarkedDeleteRims,rawExpandedApproximateCollapse,markedExpandedApproximateCollapse,hDel,hcolour,hb]
      have hs:state a=true:=(ordinary_shifted_active_rim_oriented Host π d true true raw' x y hHost hfar hraw).1
      exact ⟨a,hs,rfl⟩
    · let a:((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U):=Sum.inl (Sum.inl (y,x))
      have hfar':¬PermutationClose π (3*d+2) y x:=fun h=>hfar ((permutationClose_symm π _ _ _).mp h)
      have hDel':s(y,x)∉Del.edgeFinset:=by simpa only [Sym2.eq_swap] using hDel
      have hraw:raw' (Sum.inl s(y,x))=some (false,orientationBit y x):=by
        rw [show s(y,x)=s(x,y) from Sym2.eq_swap]
        simp [raw',raw,rawMarkedDeleteRims,rawExpandedApproximateCollapse,markedExpandedApproximateCollapse,hDel,hcolour,hb]
      have hs:state a=true:=(ordinary_shifted_active_rim_oriented Host π d true true raw' y x hHost.symm hfar' hraw).1
      refine ⟨a,hs,?_⟩
      simp [a,φ,ordinaryMixedPhysicalResource,markedPairPhysical,Sym2.eq_swap]
  left
  left
  refine ⟨hP.ne,⟨⟨Sum.inl s(x,y),hactive⟩,by simp,rfl⟩⟩
end Oberwolfach
