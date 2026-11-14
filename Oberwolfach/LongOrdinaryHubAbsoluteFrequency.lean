module

public import Oberwolfach.SampledMixedHubAbsoluteFrequency
public import Oberwolfach.LongOrdinaryHubTarget
public import Oberwolfach.LongSeedCoefficientUniformUpper
public import Oberwolfach.OrdinaryCommonHubRootCard
public import Oberwolfach.LongKeptFractionBounds

@[expose] public section
/-! A matching test at a retained ordinary hub has the desired absolute
frequency, with the actual mixed target and coefficient. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
  {E:Option (Fin K)→Type} [∀i,Fintype (E i)] [∀i,DecidableEq (E i)]

theorem long_ordinary_hub_absolute_frequency
    (hn:0<n) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (m:ℕ) (θ D p k τ t countErr γ eps:ℝ) (hθ0:0≤θ) (hθ1:θ≤1)
    (hb:∀u,(1/4:ℝ)≤longAssignedApproxOrdinaryWeight F hF K m θ u)
    (R:∀i,E i→Finset (((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)))
    (state:(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))→Bool)
    (w:∀i,E i→ℝ) (hub:∀i,E i→U) (i:Fin K) (u:U) (r:ℕ) (hr:0<r)
    (hS:∀c,(R (some i) c∩ordinaryCommonHubSpokeRoots u).card=if hub (some i) c=u then r else 0)
    (hτ:0≤τ) (herr0:0≤t+4*τ) (herrle:t+4*τ≤eps/2)
    (hcount0:0≤countErr) (hcountle:4*countErr≤(eps/2)*n)
    (hγ:0≤γ) (hγε:γ≤eps) (heps:0≤eps) (heps1:eps≤1)
    (hload:∀z,state z=true→
      |resourcePatternLoad (R (some i)) (w (some i)) (fun _ _=>true) z state-
        longAssignedMixedTarget F hF K m θ D p k (some i) z|≤
        t+τ*longAssignedMixedTarget F hF K m θ D p k (some i) z)
    (hcount:|(((ordinaryCommonHubSpokeRoots u).filter (fun v=>state v=true)).card:ℝ)-
      longAssignedApproxOrdinaryWeight F hF K m θ u*n|≤countErr)
    (hw:∀j c,0≤w j c):
    let e:{v // v∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
    let test:=mixedHubIndicator hub (some i) u
    let mass:=∑c:RestrictedResource (mixedCandidateResources R) e,
      test c.val.1 c.val.2*mixedCandidateWeight w c.val
    (1-γ)*mass≤∑c∈M,test c.val.1 c.val.2→
    (∑c∈M,test c.val.1 c.val.2)≤(1+γ)*mass→
    |((M.filter (fun c=>c.val.1=some i ∧ hub c.val.1 c.val.2=u)).card:ℝ)-
      (1-θ)*longAssignedKeptFraction F hF K θ i u*n/r|≤3*eps*n :=by
  intro e M test mass hlow hup
  let b:=longAssignedApproxOrdinaryWeight F hF K m θ
  let η:=longAssignedKeptOrdinaryContribution F hF K θ i u/b u
  have hbpos:∀u,0<b u:=by intro v;have h:=hb v;dsimp only [b];linarith
  have hη:=long_assigned_seed_coefficient_le_four hn F hF K m θ hθ0 hθ1 hb i u
  have hbal:=long_assigned_all_ordinary_seed_balance F hF K m θ hbpos i u
  have htarget:=long_kept_frequency_target_abs_le_order hn F hF θ hθ0 hθ1 i u
  have hdeg:=long_ordinary_hub_root_load_bound F hF m θ D p k t τ hτ i u (R (some i)) (w (some i)) state hη.2 hload
  have hq:(((ordinaryCommonHubSpokeRoots u).filter (fun z=>state z=true)).card:ℝ)≤n:=by
    have hh:((ordinaryCommonHubSpokeRoots u).filter (fun z=>state z=true)).card≤n:=by
      simpa only [Fintype.card_fin] using ordinary_common_hub_active_roots_card_le (V:=Fin n) u state
    exact_mod_cast hh
  exact sampled_mixed_hub_absolute_frequency R state w hub (some i) u (ordinaryCommonHubSpokeRoots u) r hr hS
    η 4 (b u) n (t+4*τ) countErr γ θ (longAssignedKeptFraction F hF K θ i u) eps hη.1 hη.2
    (by positivity) hγ hγε heps heps1 hbal hdeg hcount hq herr0 herrle hcount0 hcountle htarget hw M
    (by
      dsimp only [test,mass] at hlow
      convert hlow using 1 <;> congr 3 <;> exact Subsingleton.elim _ _)
    (by
      dsimp only [test,mass] at hup
      convert hup using 1 <;> congr 3 <;> exact Subsingleton.elim _ _)
end Oberwolfach
