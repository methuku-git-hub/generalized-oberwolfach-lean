module

public import Oberwolfach.OrdinaryAdaptiveFreshFromCleanupParent
public import Oberwolfach.OrdinaryFreshInsideBundleEvent
public import Oberwolfach.OrdinaryUniversalDeepParentsFromRawPrior

@[expose] public section
/-! A prior carrying the original raw parent event and adaptive hub weights
    extends to a fresh boundary bundle on the same earlier outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 6500000
set_option synthInstance.maxSize 8192
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_adaptive_fresh_from_raw_parent_prior
    (γ κ b B:ℝ) (hγ:0<γ) (hκ:0<κ) (hb:0<b) (hB:0≤B):
    ∃ε η ζ:ℝ,0<ε ∧ 0<η ∧ 0<ζ ∧
    ∀(p:ℝ) (hp:0<p) (hp1:p≤1) (q:ℕ)
      (εres εsup βe βh:ℝ) (hres:0<εres) (hsup:0<εsup) (hβe:0<βe) (hβh:0<βh),∃N:ℕ,
    ∀(V U Ω Γ Color:Type) [Fintype V] [Fintype U] [Fintype Ω] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U],
      N≤Fintype.card V→Fintype.card U≤Fintype.card V→
    ∀(μ:FiniteLaw Ω) (E:Ω→Prop) (e₀:ℝ),1-e₀≤μ.probability E→
    ∀(P Q₀ F:Ω→SimpleGraph V) (H₀:Ω→V→U→Prop) (X:Ω→Finset V) (Z:Ω→Finset U)
      (π:Equiv.Perm V) (d k:ℕ) (s:U→Color→ℝ) (j:Color) (raw:Ω→RawWheelOutcome V U Γ Color)
      (pR pH density tR tH Ledit:ℝ),
    let Q:=fun ω=>spanningRestriction (Q₀ ω) (X ω);
    let H:=fun ω v u=>H₀ ω v u ∧ v∈X ω ∧ u∈Z ω;
    ∀(endpointWeight:Ω→V→Sym2 (V⊕U)→ℝ) (triangleWeight:∀ω,OrdinaryCycle (P ω) 3→ℝ)
      (κe pParent Lconf δend εcount tend Kscale e:ℝ)
      (α pstar βP ηP ηH βH c Btri:ℝ),
    (∀ω,E ω→OrdinaryDeepParentMargins (P ω) (F ω) (X ω) (Z ω) γ κ b B ε η κe pParent
      pR pH density tR tH Lconf Ledit δend εcount tend Kscale e)→
    (∀ω,E ω→EndpointPhysicalParentWeights (P ω) (X ω) (X ω)ᶜ (endpointWeight ω))→
    (∀ω,E ω→OrdinaryRawHubParentPrior d k (P ω) (F ω) (X ω) (Z ω) π j s (endpointWeight ω) (triangleWeight ω)
      α pstar βP ηP ηH βH c Btri pR pH tend tR tH (raw ω))→
    (∀ω,E ω→OrdinaryCleanupParentProfiles (P ω) (Q₀ ω) (F ω) (H₀ ω) π d (X ω) (Z ω)
      pR pH density tR tH Ledit βe βh s j (raw ω))→
    (∀ω,E ω→Q₀ ω≤P ω)→
    (∀ω,E ω→∀(Q':SimpleGraph V) (H':V→U→Prop),
      OrdinaryCleanupParentProfiles (P ω) Q' (F ω) H' π d (X ω) (Z ω)
        pR pH density tR tH Ledit βe βh s j (raw ω)→
      Q'≤P ω→Nonempty (OrdinaryMixedHubWeights b B η Q' (F ω) H' (X ω) (Z ω)))→
    ∃(parent:∀ω,E ω→Nonempty (MixedFreshParentDataInsideRoots γ κ b B ε η (Q ω) (F ω)
      (ordinaryPhysicalGraph (Q ω) (H ω)) (ordinaryPhysicalGraph (F ω) (fun _ _=>False))
      (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet (H₀ ω) (Z ω) (X ω))
      (fun i=>(ordinaryBoundaryRimSet (Q₀ ω) (X ω) i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet (H₀ ω) (X ω) (Z ω) i).image Sum.inr))),
    let data:=fun ω (h:E ω)=>Classical.choice (parent ω h);
    let ν:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1);
    1-(e₀+4/(Fintype.card (V⊕U):ℝ)^q+1/(Fintype.card V:ℝ)^q)≤
      (μ.sigma (fun _=>ν)).probability (fun z=>∃hE:E z.1,
        OrdinaryFreshTriangleBoundaryEventInside (Q₀ z.1) (Q z.1) (F z.1) (H₀ z.1) (H z.1) (X z.1) (Z z.1)
          γ κ b B ε η ζ p εres εsup βe βh (data z.1 hE) z.2) := by
  obtain ⟨ε,η,ζ,hε,hη,hζ,hmain⟩:=ordinary_adaptive_fresh_from_cleanup_parent_event γ κ b B hγ hκ hb hB
  refine ⟨ε,η,ζ,hε,hη,hζ,?_⟩
  intro p hp hp1 q εres εsup βe βh hres hsup hβe hβh
  obtain ⟨N,hN⟩:=hmain p hp hp1 (2*p) (by positivity) q εres εsup βe βh hres hsup hβe hβh
  refine ⟨N,?_⟩
  intro V U Ω Γ Color _ _ _ _ _ _ _ hn hu μ E e₀ hE P Q₀ F H₀ X Z π d k s j raw
    pR pH density tR tH Ledit Q H endpointWeight triangleWeight κe pParent Lconf δend εcount tend Kscale e
    α pstar βP ηP ηH βH c Btri hmargins hparent hraw hprofile hsub hhub
  let parent:=fun ω (h:E ω)=>ordinary_universal_deep_parents_from_raw_prior (P ω) (F ω) (X ω) (Z ω) π d k j s
    (endpointWeight ω) (triangleWeight ω) γ κ b B ε η κe pParent pR pH density tR tH Lconf Ledit βe βh
    δend εcount tend Kscale e α pstar βP ηP ηH βH c Btri (raw ω)
    (hmargins ω h) (hparent ω h) (hraw ω h) (hhub ω h) (Q₀ ω) (H₀ ω) (hprofile ω h) (hsub ω h)
  refine ⟨parent,?_⟩
  intro data ν
  have hh:=hN V U Ω Γ Color hn hu μ E e₀ hE P Q₀ F H₀ X Z π d s j raw
    pR pH density tR tH Ledit hprofile parent
  exact ordinary_fresh_inside_bundle_event (μ.sigma (fun _=>ν)) E _ Q₀ Q F H₀ H X Z
    γ κ b B ε η ζ p εres εsup βe βh data hh
end Oberwolfach
