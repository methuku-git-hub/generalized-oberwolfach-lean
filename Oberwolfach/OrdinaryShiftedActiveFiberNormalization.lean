module

public import Oberwolfach.OrdinaryMixedActiveFiberTargets
public import Oberwolfach.OrdinaryShiftedActiveRimFiber
public import Oberwolfach.PhysicalEligibleFiberRestriction
public import Oberwolfach.PhysicalSampledCandidateRestriction
public import Oberwolfach.RawMarkedSpokeDisjointness

@[expose] public section
/-! On the ordinary sample restricted to manuscript-eligible physical edges,
the active typed target mass at every physical resource is exactly one. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V U Γ Color:Type} [Fintype I] [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def ordinaryPhysicalEligible (π:Equiv.Perm V) (d:ℕ):Sym2 V⊕(V×U)→Prop :=
  Sum.elim (fun e=>e∉(permutationConflictGraph π (3*d+2)).edgeFinset) (fun _=>True)

theorem ordinary_shifted_active_fiber_normalization
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (g:Γ) (j:Color)
    (raw:RawMarkedOutcome V U Γ Color) (m D p:ℝ) (hD:0<D) (hp:0<p)
    (a b:U→ℝ) (η:I→U→ℝ) (hb:∀u,0<b u)
    (hbal:∀u,m*a u+(∑i,η i u)*b u=b u) (hpdef:(∑u,(a u+b u))=D*p):
    let φ:=ordinaryMixedPhysicalResource (U:=U) π
    let good:=ordinaryPhysicalEligible (U:=U) π d
    let st:=typedMarkedResourceState (ordinaryShiftedPairRims P π d raw) (rawMarkedPairSpokes π d raw g j)
    let σ:=physicallyRestrictedState φ good st;
    ∀x:PhysicalSampledActive φ σ,
      ∑z∈Finset.univ.filter (fun z=>φ z=x.val ∧ σ z=true),
        ∑i:Option I,ordinaryMixedIdealTarget m D p a b η i z=1 :=by
  intro φ good st σ x
  obtain ⟨z,hz,hzx⟩:=x.property
  have hgood:good x.val:=by
    have hzgood:good (φ z):=by
      by_contra hh
      simp [σ,physicallyRestrictedState,hh] at hz
    simpa [hzx] using hzgood
  have hst:st z=true:=by
    have hh:good (φ z):=by simpa [hzx] using hgood
    simpa [σ,physicallyRestrictedState,hh] using hz
  have heq:(∑z∈Finset.univ.filter (fun z=>φ z=x.val ∧ σ z=true),
      ∑i:Option I,ordinaryMixedIdealTarget m D p a b η i z)=
      ∑z∈Finset.univ.filter (fun z=>φ z=x.val ∧ st z=true),
        ∑i:Option I,ordinaryMixedIdealTarget m D p a b η i z:=by
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv:φ v=x.val
    · simp [hv,σ,physicallyRestrictedState,hgood]
    · simp [hv]
  rw [heq]
  rw [←hzx] at hgood ⊢
  cases z with
  | inl e=>
    cases e with
    | inl e=>
      obtain ⟨v,w⟩:=e
      have hs:¬PermutationClose π (3*d) v w ∧ P.Adj v w ∧
          raw (Sum.inl s(v,w))=some (false,orientationBit v w):=by
        simpa only [st,typedMarkedResourceState,ordinaryShiftedPairRims,Sum.elim_inl,decide_eq_true_eq] using hst
      have hf:¬PermutationClose π (3*d+2) v w:=by
        intro hclose
        apply hgood
        change s(v,w)∈(permutationConflictGraph π (3*d+2)).edgeFinset
        exact SimpleGraph.mem_edgeFinset.mpr ⟨hs.2.1.ne,hclose⟩
      have hflags:=ordinary_shifted_active_rim_oriented P π d g j raw v w hs.2.1 hf hs.2.2
      simpa only [φ,ordinaryMixedPhysicalResource,Sum.elim_inl,markedPairPhysical] using
        ordinary_mixed_active_rim_fiber_target π m D p hD hp a b η hb hbal hpdef st v w hs.2.1.ne
          hflags.1 hflags.2.1 hflags.2.2.1 hflags.2.2.2
    | inr e=>
      obtain ⟨v,w⟩:=e
      have hs:¬PermutationClose π (3*d) v w ∧ P.Adj v (π w) ∧
          raw (Sum.inl s(v,π w))=some (false,orientationBit v (π w)):=by
        simpa only [st,typedMarkedResourceState,ordinaryShiftedPairRims,Sum.elim_inl,Sum.elim_inr,decide_eq_true_eq] using hst
      have hf:¬PermutationClose π (3*d+2) v (π w):=by
        intro hclose
        apply hgood
        change s(v,π w)∈(permutationConflictGraph π (3*d+2)).edgeFinset
        exact SimpleGraph.mem_edgeFinset.mpr ⟨hs.2.1.ne,hclose⟩
      have hflags:=ordinary_shifted_active_rim_oriented P π d g j raw v (π w) hs.2.1 hf hs.2.2
      simpa only [φ,ordinaryMixedPhysicalResource,Sum.elim_inl,markedPairPhysical,Sum.elim_inr] using
        ordinary_mixed_active_rim_fiber_target π m D p hD hp a b η hb hbal hpdef st v (π w) hs.2.1.ne
          hflags.1 hflags.2.1 hflags.2.2.1 hflags.2.2.2
  | inr e=>
    obtain ⟨flag,v,u⟩:=e
    have hactive:st (Sum.inr (false,v,u))=true ∨ st (Sum.inr (true,v,u))=true:=by
      cases flag <;> simp_all
    have hdis:¬(st (Sum.inr (false,v,u))=true ∧ st (Sum.inr (true,v,u))=true):=by
      intro h
      have hh:rawMarkedPairSpokes π d raw g j false v u ∧ rawMarkedPairSpokes π d raw g j true v u:=by
        simpa only [st,typedMarkedResourceState,Sum.elim_inr,decide_eq_true_eq] using h
      exact rawMarkedSpokes_disjoint π d (fun e=>raw (Sum.inr e)) g j v u hh
    simpa only [φ,ordinaryMixedPhysicalResource,Sum.elim_inr] using
      ordinary_mixed_active_spoke_fiber_target π m D p a b η st v u (hb u) (hbal u) hactive hdis
end Oberwolfach
