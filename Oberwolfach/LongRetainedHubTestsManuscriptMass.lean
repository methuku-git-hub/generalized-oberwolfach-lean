module

public import Oberwolfach.LongRetainedHubTestsFromPatterns
public import Oberwolfach.LongAssignedHubTestManuscriptPatterns

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U V:Type} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
  {E:Option (Fin K)→Type} [∀i,Fintype (E i)] [∀i,DecidableEq (E i)]

theorem long_retained_hub_tests_manuscript_mass_from_patterns
    (hn:0<n) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (m:ℕ) (hK:0<K) (hK3:3≤K) (θ:ℝ) (hθ0:0<θ) (hθ:θ≤1/10)
    (b:U→ℝ) (hbdef:∀u,b u=longAssignedApproxOrdinaryWeight F hF K m θ u)
    (hb:∀u,0<b u ∧ b u≤1) (pstar:ℝ) (hpstar:0<pstar) (hbstar:∀u,pstar≤b u)
    (R:∀j,E j→Finset V) (state:V→Bool) (w:∀j,E j→ℝ) (hub:∀j,E j→U)
    (S:U→Finset V)
    (hS:∀i u c,(R (some i) c∩S u).card=if hub (some i) c=u then longAssignedPaddedLength i else 0)
    (τ t countErr:ℝ) (hτ:τ≤1/16) (ht:t≤θ/(3200*(K:ℝ)))
    (hdeg:∀i u,θ/(100*(K:ℝ))≤longAssignedKeptFraction F hF K θ i u→∀v∈S u,state v=true→
      |resourcePatternLoad (R (some i)) (w (some i)) (fun _ _=>true) v state-
        longAssignedKeptOrdinaryContribution F hF K θ i u/b u|≤
        t+τ*(longAssignedKeptOrdinaryContribution F hF K θ i u/b u))
    (hcount:∀u,|(((S u).filter (fun v=>state v=true)).card:ℝ)-b u*n|≤countErr)
    (hcountErr:countErr≤pstar*n/16):
    let e: {v:V // v∈bernoulliVertexSet state}↪V := Function.Embedding.subtype _
    ∀z:LongRetainedHubTest F hF K θ,
      θ*(n:ℝ)/(200*(K:ℝ)*(K:ℝ))≤
        ∑c:RestrictedResource (mixedCandidateResources R) e,
          longRetainedHubIndicator F hF θ hub z c.val*mixedCandidateWeight w c.val :=by
  intro e z
  let i:=z.val.1
  let u:=z.val.2
  have hK':0<(K:ℝ):=by exact_mod_cast hK
  have hb':∀u,0<longAssignedApproxOrdinaryWeight F hF K m θ u ∧
      longAssignedApproxOrdinaryWeight F hF K m θ u≤1:=by
    intro u
    rw [←hbdef u]
    exact hb u
  have hη:=long_retained_hub_coefficient_lower F hF K m hK θ hθ0 (by linarith) hb' i u z.property
  have hsmall:t≤(longAssignedKeptOrdinaryContribution F hF K θ i u/
      longAssignedApproxOrdinaryWeight F hF K m θ u)/16:=by
    have heq:θ/(3200*(K:ℝ))=(θ/(200*(K:ℝ)))/16:=by ring
    rw [heq] at ht
    linarith
  have hcsmall:countErr≤longAssignedApproxOrdinaryWeight F hF K m θ u*n/16:=by
    have hh:=mul_le_mul_of_nonneg_right (hbstar u) (Nat.cast_nonneg n)
    rw [hbdef u] at hh
    linarith
  have hr:0<longAssignedPaddedLength i:=by have h:=long_assigned_padded_length_valid i;omega
  have hrmax:((longAssignedPaddedLength i:ℕ):ℝ)≤K:=by exact_mod_cast long_assigned_padded_length_upper hK3 i
  have hload:∀v∈S u,state v=true→
      |resourcePatternLoad (R (some i)) (w (some i)) (fun _ _=>true) v state-
        longAssignedKeptOrdinaryContribution F hF K θ i u/
          longAssignedApproxOrdinaryWeight F hF K m θ u|≤
        t+τ*(longAssignedKeptOrdinaryContribution F hF K θ i u/
          longAssignedApproxOrdinaryWeight F hF K m θ u):=by
    simpa only [hbdef u] using hdeg i u z.property
  have hcount':|(((S u).filter (fun v=>state v=true)).card:ℝ)-
      longAssignedApproxOrdinaryWeight F hF K m θ u*n|≤countErr:=by simpa only [hbdef u] using hcount u
  exact long_assigned_hub_test_manuscript_mass_from_sampled_patterns hn F hF m hK θ hθ0 hθ (fun u=>(hb' u).1)
    R state w hub i (some i) u (S u) (longAssignedPaddedLength i) hr K hrmax z.property
    (hS i u) τ t countErr hτ hsmall hload hcount' hcsmall
end Oberwolfach
