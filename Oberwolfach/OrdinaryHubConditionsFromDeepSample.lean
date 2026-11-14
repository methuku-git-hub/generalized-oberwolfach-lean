module

public import Oberwolfach.OrdinaryHubDeepRowsFromCleanup
public import Oberwolfach.EndpointRelativeCounts
public import Oberwolfach.OrdinaryBoundaryRootSets

@[expose] public section
/-! The same deeper row event yields hub class size and local-root
common-neighborhood estimates for every outer hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_hub_conditions_from_deep_sample
    (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ)
    (γ κ p pR pH density tR tH L Ledit βe βh ε:ℝ) (σ:RawWheelOutcome V U Γ Color)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d A B pR pH density tR tH Ledit βe βh s j σ)
    (deep:RawOrdinaryRows P π d 3 A pR s j tR σ)
    (hp:0<p) (hp1:p≤1) (hpR:p≤pR) (hpH:p≤pH) (hdensity:(3/4:ℝ)≤density)
    (hL:0≤L) (hLedit:0≤Ledit) (hLA:L≤(A.card:ℝ)/24) (hF:∀v,(F.degree v:ℝ)≤L)
    (hbudget:tR+4*Ledit≤ε*A.card) (hε:ε≤p^4/16)
    (hγscale:γ*Fintype.card V≤(p^4/16)*A.card)
    (hκscale:κ*Fintype.card V≤(p^4/16)*A.card):
    (∀j:{u:U // u∉B},κ*Fintype.card V≤((ordinaryBoundaryHubSet H B A j).card:ℝ)) ∧
    (∀j:{u:U // u∉B},∀S:Finset V,S⊆ordinaryBoundaryHubSet H B A j→S.card≤3→
      γ*Fintype.card V≤((common (ordinaryBoundaryHubSet H B A j) S
        (fun x=>(spanningRestriction Q A).neighborFinset x)).card:ℝ)):=by
  have hrows:=ordinary_hub_deep_rows_from_cleanup P Q F H A B π d j s pR pH density tR tH Ledit βe βh ε σ
    profile deep hLedit hbudget
  have hdeg:∀v,(3/4:ℝ)*A.card≤((A∩P.neighborFinset v).card:ℝ):=by
    intro v
    exact (mul_le_mul_of_nonneg_right hdensity (Nat.cast_nonneg _)).trans (profile.parent_min_degree v)
  have hbound (u:U) (S:Finset V) (hS:S.card≤3):
      (p^4/16)*A.card≤((common (A.filter (fun v=>H v u)) S (fun v=>Q.neighborFinset v)).card:ℝ):=by
    have hc:=endpoint_surviving_common_lower P F A S L hS hL hLA (fun v _=>hdeg v) (fun v _=>hF v)
    have hpow:p^4≤pR^S.card*pH:=by
      calc
        _≤p^(S.card+1):=pow_le_pow_of_le_one hp.le hp1 (by omega)
        _=p^S.card*p:=by rw [pow_succ]
        _≤pR^S.card*pH:=mul_le_mul (pow_le_pow_left₀ hp.le hpR _) hpH hp.le (pow_nonneg (hp.le.trans hpR) _)
    have hm:=mul_le_mul hpow hc (by positivity:(0:ℝ)≤(A.card:ℝ)/8)
      (mul_nonneg (pow_nonneg (hp.le.trans hpR) _) (hp.le.trans hpH))
    have he:=mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg A.card)
    have hr:=hrows u S hS
    nlinarith only [hm,he,hr]
  constructor
  · intro j₀
    have hh:=hbound j₀.val ∅ (by simp)
    simpa [ordinaryBoundaryHubSet,common] using hκscale.trans hh
  · intro j₀ S hST hS
    have hSA:S⊆A:=by
      intro v hv
      exact (Finset.mem_filter.mp (hST hv)).1
    have he:common (ordinaryBoundaryHubSet H B A j₀) S
        (fun v=>(spanningRestriction Q A).neighborFinset v)=
        common (A.filter (fun v=>H v j₀.val)) S (fun v=>Q.neighborFinset v):=by
      ext v
      simp only [ordinaryBoundaryHubSet,mem_common_iff,Finset.mem_filter,SimpleGraph.mem_neighborFinset,
        spanningRestriction_adj]
      constructor
      · rintro ⟨⟨hv,hHv⟩,hs⟩
        exact ⟨⟨hv,hHv⟩,fun x hx=>(hs x hx).1⟩
      · rintro ⟨⟨hv,hHv⟩,hs⟩
        exact ⟨⟨hv,hHv⟩,fun x hx=>⟨hs x hx,hSA hx,hv⟩⟩
    rw [he]
    exact hγscale.trans (hbound j₀.val S hS)
end Oberwolfach
