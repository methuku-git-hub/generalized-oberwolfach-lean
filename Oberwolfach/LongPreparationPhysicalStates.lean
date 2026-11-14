module

public import Oberwolfach.LongPreparationIneligibleGraph
public import Oberwolfach.MarkedFinitePhysicalDeletion
public import Oberwolfach.MarkedExpandedRawLaw

@[expose] public section
/-! Physical selected, approximate and unassigned edges remain in their
original categorical states after passing to an unordered graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
  [Fintype Γ] [Fintype Color]

def longPhysicalStateGraph (P:SimpleGraph V)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (T:Finset (Fin 6)):SimpleGraph V where
  Adj x y:=P.Adj x y ∧ (σ (Sum.inl s(x,y))).1∈T
  symm:=⟨by
    intro x y h
    refine ⟨h.1.symm,?_⟩
    rw [show s(y,x)=s(x,y) from Sym2.eq_swap]
    exact h.2⟩
  loopless:=⟨by intro x h;exact P.loopless.irrefl x h.1⟩

def longSelectedPhysicalGraph (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e):SimpleGraph V:=
  let raw:RawMarkedOutcome V U Γ Color:=fun e=>rawExpandedMarkedCollapse e (σ e)
  markedSampleArcSetGraph P π d raw Finset.univ

theorem selected_state_outside_ineligible_is_selected
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (x y:V) (hP:P.Adj x y) (hfar:¬(longPreparationIneligibleGraph P π d).Adj x y)
    (hsel:(σ (Sum.inl s(x,y))).1=0 ∨ (σ (Sum.inl s(x,y))).1=1):
    (longSelectedPhysicalGraph P π d σ).Adj x y:=by
  let raw:RawMarkedOutcome V U Γ Color:=fun e=>rawExpandedMarkedCollapse e (σ e)
  have hbits:orientationBit x y=(σ (Sum.inl s(x,y))).2 ∨ orientationBit y x=(σ (Sum.inl s(x,y))).2:=by
    have hh:=orientationBit_ne_swap x y hP.ne
    cases hx:orientationBit x y <;> cases hy:orientationBit y x <;>
      cases hb:(σ (Sum.inl s(x,y))).2 <;> simp_all
  have hno1:¬PermutationClose π (3*d) x y:=by
    intro h;exact hfar ⟨hP,Or.inl h⟩
  have hno2:¬PermutationClose π (3*d) x (π.symm y):=by
    intro h;exact hfar ⟨hP,Or.inr (Or.inl h)⟩
  have hno3:¬PermutationClose π (3*d) y (π.symm x):=by
    intro h;exact hfar ⟨hP,Or.inr (Or.inr h)⟩
  rcases hsel with hstate|hstate <;> rcases hbits with hbit|hbit
  · have hr:markedPhysicalRim P π (3*d) (fun e=>raw (Sum.inl e)) false x y=1:=by
      apply (markedPhysicalRim_eq_one_iff P π (3*d) _ false x y).mpr
      refine ⟨hno1,hP,?_⟩
      simp [raw,rawExpandedMarkedCollapse,markedExpandedPhysicalCollapse,hstate,hbit]
    let e:MarkedSampleArc P π (3*d) (fun e=>raw (Sum.inl e)) false:=⟨(x,y),hr⟩
    have hh: s(x,y)∈(markedSampleArcSetGraph P π d raw Finset.univ).edgeFinset:=by
      simpa only [Sum.elim_inl] using
        (markedSampleArcSetGraph_coordinate P π d raw Finset.univ (Sum.inl e)).mpr (Finset.mem_univ _)
    exact SimpleGraph.mem_edgeFinset.mp hh
  · have hr:markedPhysicalRim P π (3*d) (fun e=>raw (Sum.inl e)) false y x=1:=by
      apply (markedPhysicalRim_eq_one_iff P π (3*d) _ false y x).mpr
      refine ⟨fun h=>hno1 ((permutationClose_symm π (3*d) y x).mp h),hP.symm,?_⟩
      change raw (Sum.inl s(y,x))=some (false,orientationBit y x)
      rw [show s(y,x)=s(x,y) from Sym2.eq_swap]
      simp [raw,rawExpandedMarkedCollapse,markedExpandedPhysicalCollapse,hstate,hbit]
    let e:MarkedSampleArc P π (3*d) (fun e=>raw (Sum.inl e)) false:=⟨(y,x),hr⟩
    have hh: s(y,x)∈(markedSampleArcSetGraph P π d raw Finset.univ).edgeFinset:=by
      simpa only [Sum.elim_inl] using
        (markedSampleArcSetGraph_coordinate P π d raw Finset.univ (Sum.inl e)).mpr (Finset.mem_univ _)
    exact (SimpleGraph.mem_edgeFinset.mp hh).symm
  · have hr:markedPhysicalRim P π (3*d) (fun e=>raw (Sum.inl e)) true x (π.symm y)=1:=by
      apply (markedPhysicalRim_eq_one_iff P π (3*d) _ true x (π.symm y)).mpr
      refine ⟨hno2,by simpa using hP,?_⟩
      change raw (Sum.inl s(x,π (π.symm y)))=some (true,orientationBit x (π (π.symm y)))
      rw [Equiv.apply_symm_apply]
      simp [raw,rawExpandedMarkedCollapse,markedExpandedPhysicalCollapse,hstate,hbit]
    let e:MarkedSampleArc P π (3*d) (fun e=>raw (Sum.inl e)) true:=⟨(x,π.symm y),hr⟩
    have hh: s(x,y)∈(markedSampleArcSetGraph P π d raw Finset.univ).edgeFinset:=by
      simpa only [Sum.elim_inr,e,Equiv.apply_symm_apply] using
        (markedSampleArcSetGraph_coordinate P π d raw Finset.univ (Sum.inr e)).mpr (Finset.mem_univ _)
    exact SimpleGraph.mem_edgeFinset.mp hh
  · have hr:markedPhysicalRim P π (3*d) (fun e=>raw (Sum.inl e)) true y (π.symm x)=1:=by
      apply (markedPhysicalRim_eq_one_iff P π (3*d) _ true y (π.symm x)).mpr
      refine ⟨hno3,by simpa using hP.symm,?_⟩
      change raw (Sum.inl s(y,π (π.symm x)))=some (true,orientationBit y (π (π.symm x)))
      rw [Equiv.apply_symm_apply]
      rw [show s(y,x)=s(x,y) from Sym2.eq_swap]
      simp [raw,rawExpandedMarkedCollapse,markedExpandedPhysicalCollapse,hstate,hbit]
    let e:MarkedSampleArc P π (3*d) (fun e=>raw (Sum.inl e)) true:=⟨(y,π.symm x),hr⟩
    have hh: s(y,x)∈(markedSampleArcSetGraph P π d raw Finset.univ).edgeFinset:=by
      simpa only [Sum.elim_inr,e,Equiv.apply_symm_apply] using
        (markedSampleArcSetGraph_coordinate P π d raw Finset.univ (Sum.inr e)).mpr (Finset.mem_univ _)
    exact (SimpleGraph.mem_edgeFinset.mp hh).symm
end Oberwolfach
