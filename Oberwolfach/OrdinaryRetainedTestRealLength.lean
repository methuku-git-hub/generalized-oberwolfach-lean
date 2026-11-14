module

public import Oberwolfach.OrdinaryAssignedRetainedHubTests
public import Oberwolfach.OrdinaryAssignedNonretainedZero

@[expose] public section
/-! A retained hub test refers to an actual component length at that hub;
the formal dummy triangle indices cannot be retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_retained_test_real_length
    (hn:0<n) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (hK:0<K) (i₀:Fin K) (rsv θ:ℝ) (hs0:0≤rsv) (hθ:0<θ)
    (z:OrdinaryAssignedRetainedHubTest F hF i₀ rsv θ):
    z.val.1∈longRetainedSeedIndices F hF K θ ∧
    longPaddedSeedExponent z.val.1+2=z.val.1.val+1 ∧
    (z.val.1.val+1)∈Allowed ∧
    ∃v:Fin n,Fintype.card ((F z.val.2).connectedComponentMk v)=z.val.1.val+1 :=by
  let i:=z.val.1
  let u:=z.val.2
  have hK':0<(K:ℝ):=by exact_mod_cast hK
  have hthreshold:0<θ/(100*(K:ℝ)):=by positivity
  have hretain:θ/(100*(K:ℝ))≤ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i:=z.property
  have hraw:θ/(100*(K:ℝ))≤ordinaryAssignedFraction F hF K u (some i):=by
    by_cases hindex:i=i₀
    · rw [hindex]
      simp only [ordinaryAssignedKeptFraction,hindex,ite_true] at hretain
      split_ifs at hretain <;> linarith
    · simp only [ordinaryAssignedKeptFraction,hindex,ite_false,sub_zero] at hretain
      split_ifs at hretain <;> linarith
  have hi:i∈longRetainedSeedIndices F hF K θ:=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨u,hraw⟩⟩
  have hh:=long_preparation_retained_length_allowed hn (F u) (hF u) Allowed (hAllowed u) K hK θ hθ i hraw
  refine ⟨hi,?_,hh.2.1,hh.2.2⟩
  rw [long_padded_seed_length_eq_exponent]
  exact long_assigned_padded_length_true i hh.1
end Oberwolfach
