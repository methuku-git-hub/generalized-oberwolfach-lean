module

public import Oberwolfach.LongAssignedPaddedLengths
public import Oberwolfach.LongPreparationRetainedLengths
public import Oberwolfach.LongShortSeedZeroComponent

@[expose] public section
/-! The padded finite length list contains every retained length, and only
retained lengths require fractional cycle weights. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U:Type} [Fintype U]

def longRetainedSeedIndices
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2) (K:ℕ) (θ:ℝ):Finset (Fin K):=
  Finset.univ.filter (fun i=>∃u,θ/(100*(K:ℝ))≤ordinaryAssignedFraction F hF K u (some i))

def longPaddedSeedExponent {K:ℕ} (i:Fin K):ℕ:=longAssignedPaddedLength i-2

theorem long_padded_seed_exponent_positive {K:ℕ} (i:Fin K):1≤longPaddedSeedExponent i:=by
  have h:=long_assigned_padded_length_valid i
  unfold longPaddedSeedExponent
  omega

theorem long_padded_seed_length_eq_exponent {K:ℕ} (i:Fin K):
    longPaddedSeedExponent i+2=longAssignedPaddedLength i:=by
  have h:=long_assigned_padded_length_valid i
  unfold longPaddedSeedExponent
  omega

theorem long_retained_padded_length_allowed
    (hn:0<n) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (K:ℕ) (hK:0<K) (θ:ℝ) (hθ:0<θ):
    ∀i:Fin K,i∈longRetainedSeedIndices F hF K θ→
      longPaddedSeedExponent i+2∈Allowed :=by
  intro i hi
  obtain ⟨u,hu⟩:=(Finset.mem_filter.mp hi).2
  have hh:=long_preparation_retained_length_allowed hn (F u) (hF u) Allowed (hAllowed u) K hK θ hθ i hu
  rw [long_padded_seed_length_eq_exponent]
  have heq:longAssignedPaddedLength i=i.val+1:=by
    unfold longAssignedPaddedLength
    exact max_eq_right hh.1
  simpa only [heq] using hh.2.1

theorem long_nonretained_seed_exact_target
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (K m:ℕ) (θ D p:ℝ) (i:Fin K) (hi:i∉longRetainedSeedIndices F hF K θ)
    {C:Type} [Fintype C] (hub:C→U) (base:C→ℝ) (R:C→Finset ((Fin n×Fin n)⊕(Fin n×U)))
    (state:((Fin n×Fin n)⊕(Fin n×U))→Bool) (root:(Fin n×Fin n)⊕(Fin n×U)):
    resourcePatternLoad R (fun c=>(longAssignedKeptOrdinaryContribution F hF K θ i (hub c)/
      longAssignedApproxOrdinaryWeight F hF K m θ (hub c))*base c)
      (fun _ _=>true) root state = ordinarySeedRootTarget D p θ (longAssignedKeptFraction F hF K θ i)
        (fun u=>longAssignedKeptOrdinaryContribution F hF K θ i u/
          longAssignedApproxOrdinaryWeight F hF K m θ u) root :=by
  apply long_unretained_ordinary_seed_exact_target F hF K m θ D p i _ hub base R state root
  simpa only [longRetainedSeedIndices,Finset.mem_filter,Finset.mem_univ,true_and] using hi
end Oberwolfach
