module

public import Oberwolfach.RetainedRelativeFrequencyMargin

@[expose] public section
/-! The actual positive-support matching has the relative per-hub count
error needed for the component assignment. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longRawRelativeFrequencyFinDecidable (n:ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_raw_absolute_to_relative_frequency (hK:0<K)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2) (m d:ℕ) (θ D:ℝ)
    (hθ:0≤θ) (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (ni:Fin K→ℕ) (hni:∀i,1≤ni i) (w:∀i,OrdinaryCycle P (ni i+2)→ℝ)
    (wM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→ℝ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool) (eps lam:ℝ)
    (hlam:0≤lam) (heps:eps≤lam*(θ/(100*(K:ℝ)^2))):
    let ℓ:=fun i=>ni i+2
    let state:=typedMarkedResourceState (rawMarkedPairRims P π d raw) (rawMarkedPairSpokes π d raw g j)
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    let wO:=longAssignedOrdinarySeed F hF K m d θ D P π ni hni w
    let wmix:=longMixedSeedWeight wM wO
    let hub:=fun c:RestrictedResource (mixedCandidateResources R) e=>longRawSeedHub π d m ℓ c.val.1 c.val.2
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
    (∀c∈M,0<mixedCandidateWeight wmix c.val) →
    (∀u i, θ/(100*(K:ℝ))≤longAssignedKeptFraction F hF K θ i u →
      let t:=longAssignedKeptFraction F hF K θ i u*(n:ℝ)/((i.val+1:ℕ):ℝ)
      |(((M.filter (fun c=>c.val.1=some i ∧ hub c=u)).card:ℝ)-(1-θ)*t)|≤eps*n) →
    ∀u i,
      let t:=longAssignedKeptFraction F hF K θ i u*(n:ℝ)/((i.val+1:ℕ):ℝ)
      |(((M.filter (fun c=>c.val.1=some i ∧ hub c=u)).card:ℝ)-(1-θ)*t)|≤lam*t :=by
  intro ℓ state e R wO wmix hub M hpos herr u i t
  rcases long_kept_fraction_zero_or_retained F hF θ i u with hzero|hret
  · have hc:=long_discarded_hub_selected_zero F hF m d θ D P π ni hni w wM raw g j M i u hpos hzero
    have hc' : (M.filter (fun c=>c.val.1=some i ∧ hub c=u)).card=0 :=by
      convert hc using 1 <;> congr 1 <;> ext c <;>
        simp only [Finset.mem_filter,hub,ℓ]
    dsimp only [t]
    simp only [hzero,zero_mul,mul_zero,zero_div,sub_zero,abs_zero,le_refl,hc',Nat.cast_zero]
  · have ht:=retained_target_lower_bound n K (i.val+1) θ (longAssignedKeptFraction F hF K θ i u)
      hK (by omega) (by exact Nat.succ_le_of_lt i.isLt) hθ hret
    have hbound: (θ/(100*(K:ℝ)^2))*(n:ℝ)≤t:=by
      dsimp only [t]
      convert ht using 1 <;> ring
    exact absolute_to_relative_target_error _ _ t n (θ/(100*(K:ℝ)^2)) eps lam
      (by positivity) hlam hbound heps (herr u i hret)
end Oberwolfach
