module

public import Oberwolfach.OrderedOrdinarySpokeStability
public import Oberwolfach.RetainedMarkedSpokeChanges
public import Oberwolfach.BernoulliVertexSampling

@[expose] public section
/-! Uniform start retention changes each ordered ordinary seed load by a
bounded amount on the original resource domain and with fixed weights. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U] {m b:ℕ} {π:Equiv.Perm V}

theorem retained_ordinary_seed_load_stability
    (hm:2≤m) (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (w:OrderedOrdinaryWheel (U:=U) π b (m+1)→ℝ) (B ζ:ℝ) (hB:0≤B) (hζ:0≤ζ)
    (hw:∀W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
    (R:V×V→Prop) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Γ Color)
    (g₀:Γ) (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ g₀) t)
    (good:RetainedRestrictionGood π d σ g₀ t (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ J)
    (g:Γ) (j:Color) (root:(V×V)⊕(V×U)):
    |resourceRootOmittedLoad orderedOrdinaryResources w
      (ordinaryPotentialKeep R (retainedRawMarkedSpokes π d σ g₀ t J g j false)) root-
     resourceRootOmittedLoad orderedOrdinaryResources w
      (ordinaryPotentialKeep R (rawMarkedSpokes π d σ g j false)) root|≤
      3*((m:ℝ)+1)^3*B*ζ := by
  have hc:=retainedMarkedSpokes_restriction_changes π d σ g₀ t J
    (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ good g j ()
  have hcol : ∀ u,(∑ v,bipAdj (fun x u=>¬(rawMarkedSpokes π d σ g j false x u ↔
      retainedRawMarkedSpokes π d σ g₀ t J g j false x u)) v u)≤ζ*(Fintype.card V:ℝ) := by
    intro u
    simpa using hc.1 false u
  have hrow : ∀ v,(∑ u,bipAdj (fun x u=>¬(rawMarkedSpokes π d σ g j false x u ↔
      retainedRawMarkedSpokes π d σ g₀ t J g j false x u)) v u)≤ζ*(Fintype.card V:ℝ) := by
    intro v
    have hh : (∑ u,bipAdj (fun x u=>¬(rawMarkedSpokes π d σ g j false x u ↔
        retainedRawMarkedSpokes π d σ g₀ t J g j false x u)) v u)≤ζ*(Fintype.card U:ℝ) := by
      simpa using hc.2 false v
    have hcard:(Fintype.card U:ℝ)≤Fintype.card V:=by exact_mod_cast hu
    exact hh.trans (mul_le_mul_of_nonneg_left hcard hζ)
  have hnpos:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
  have hd:0≤ζ*(Fintype.card V:ℝ):=mul_nonneg hζ hnpos.le
  cases root with
  | inl xy =>
    rcases xy with ⟨x,y⟩
    have hh:=ordered_ordinary_spoke_stability_rim hm hn hu w B (ζ*(Fintype.card V:ℝ)) hB hd hw R
      (rawMarkedSpokes π d σ g j false) (retainedRawMarkedSpokes π d σ g₀ t J g j false) hrow hcol x y
    have heq:3*((m:ℝ)+1)^3*B*(ζ*(Fintype.card V:ℝ))/Fintype.card V=
      3*((m:ℝ)+1)^3*B*ζ := by field_simp
    simpa only [heq] using hh
  | inr vu =>
    rcases vu with ⟨v,u⟩
    have hh:=ordered_ordinary_spoke_stability_spoke hm hn w B (ζ*(Fintype.card V:ℝ)) hB hd hw R
      (rawMarkedSpokes π d σ g j false) (retainedRawMarkedSpokes π d σ g₀ t J g j false) hrow hcol v u
    have heq:((m:ℝ)+1)^2*B*(ζ*(Fintype.card V:ℝ))/Fintype.card V=
      ((m:ℝ)+1)^2*B*ζ := by field_simp
    rw [heq] at hh
    have hpow:((m:ℝ)+1)^2≤((m:ℝ)+1)^3:=by
      have hb:(1:ℝ)≤(m:ℝ)+1:=by have hh:(0:ℝ)≤m:=Nat.cast_nonneg m;linarith
      calc
        _ = ((m:ℝ)+1)^2*1:=by ring
        _ ≤ ((m:ℝ)+1)^2*((m:ℝ)+1):=mul_le_mul_of_nonneg_left hb (by positivity)
        _ = _:=by ring
    have hpos:0≤((m:ℝ)+1)^3*B*ζ:=by positivity
    nlinarith [mul_le_mul_of_nonneg_right hpow (mul_nonneg hB hζ)]
/-- Pattern and root-omitted notation describe exactly the same ordinary
seed load for the realised spoke and rim state. -/
theorem ordinary_seed_root_load_eq_pattern
    (w:OrderedOrdinaryWheel (U:=U) π b (m+1)→ℝ)
    (R:V×V→Prop) (H:V→U→Prop) (root:(V×V)⊕(V×U)):
    resourceRootOmittedLoad orderedOrdinaryResources w (ordinaryPotentialKeep R H) root =
      resourcePatternLoad orderedOrdinaryResources w (fun _ _=>true) root
        (fun e=>decide (ordinaryPotentialKeep R H e)) := by
  rw [←bernoulli_root_load_pattern]
  congr 1
  funext x
  apply propext
  simp

theorem retained_ordinary_seed_pattern_stability
    (hm:2≤m) (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (w:OrderedOrdinaryWheel (U:=U) π b (m+1)→ℝ) (B ζ:ℝ) (hB:0≤B) (hζ:0≤ζ)
    (hw:∀W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
    (R:V×V→Prop) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Γ Color)
    (g₀:Γ) (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ g₀) t)
    (good:RetainedRestrictionGood π d σ g₀ t (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ J)
    (g:Γ) (j:Color) (root:(V×V)⊕(V×U)):
    |resourcePatternLoad orderedOrdinaryResources w (fun _ _=>true) root
        (fun e=>decide (ordinaryPotentialKeep R (retainedRawMarkedSpokes π d σ g₀ t J g j false) e))-
     resourcePatternLoad orderedOrdinaryResources w (fun _ _=>true) root
        (fun e=>decide (ordinaryPotentialKeep R (rawMarkedSpokes π d σ g j false) e))|≤
      3*((m:ℝ)+1)^3*B*ζ := by
  rw [←ordinary_seed_root_load_eq_pattern,←ordinary_seed_root_load_eq_pattern]
  exact retained_ordinary_seed_load_stability hm hn hu w B ζ hB hζ hw R d σ g₀ t J good g j root
end Oberwolfach
