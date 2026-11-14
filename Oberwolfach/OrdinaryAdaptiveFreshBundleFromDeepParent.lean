module

public import Oberwolfach.OrdinaryAdaptiveFreshFromDeepParentEvent
public import Oberwolfach.OrdinaryFreshInsideBundleEvent

@[expose] public section
/-! The matching/deep parent event is retained when the fresh boundary
sample produces its full triangle-factor and cleanup bundle. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3000000
set_option synthInstance.maxSize 8192
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_adaptive_fresh_bundle_from_deep_parent_event
    (γ κ b B:ℝ) (hγ:0<γ) (hκ:0<κ) (hb:0<b) (hB:0≤B):
    ∃ε η ζ:ℝ,0<ε ∧ 0<η ∧ 0<ζ ∧
    ∀(p:ℝ) (hp:0<p) (hp1:p≤1) (q:ℕ)
      (εres εsup βe βh:ℝ) (hres:0<εres) (hsup:0<εsup) (hβe:0<βe) (hβh:0<βh),∃N:ℕ,
    ∀(V U Ω Γ Color:Type) [Fintype V] [Fintype U] [Fintype Ω] [Fintype Γ] [Fintype Color] [DecidableEq V] [DecidableEq U],
      N≤Fintype.card V→Fintype.card U≤Fintype.card V→
    ∀(μ:FiniteLaw Ω) (E:Ω→Prop) (e₀:ℝ),1-e₀≤μ.probability E→
    ∀(P Q₀ F:Ω→SimpleGraph V) (H₀:Ω→V→U→Prop) (X:Ω→Finset V) (Z:Ω→Finset U)
      (π:Equiv.Perm V) (d:ℕ) (s:U→Color→ℝ) (j:Color) (raw:Ω→RawWheelOutcome V U Γ Color)
      (pR pH density tR tH Ledit:ℝ),
    let Q:=fun ω=>spanningRestriction (Q₀ ω) (X ω);
    let H:=fun ω v u=>H₀ ω v u ∧ v∈X ω ∧ u∈Z ω;
    ∀(endpointWeight:Ω→V→Sym2 (V⊕U)→ℝ)
      (κe pParent Lconf δend εcount tend Kscale:ℝ),
    ∀(hinputs:∀ω,E ω→OrdinaryDeepParentIngredients (P ω) (Q₀ ω) (F ω) (H₀ ω) (X ω) (Z ω) π d j s
      (endpointWeight ω) γ κ b B ε η κe pParent pR pH density tR tH Lconf Ledit βe βh δend εcount tend Kscale (raw ω)),
    ∀(hdeep:∀ω,E ω→∀(Q':SimpleGraph V) (H':V→U→Prop),
      OrdinaryDeepParentIngredients (P ω) Q' (F ω) H' (X ω) (Z ω) π d j s
        (endpointWeight ω) γ κ b B ε η κe pParent pR pH density tR tH Lconf Ledit βe βh δend εcount tend Kscale (raw ω)→
      Nonempty (MixedFreshParentDataInsideRoots γ κ b B ε η (spanningRestriction Q' (X ω)) (F ω)
        (ordinaryPhysicalGraph (spanningRestriction Q' (X ω)) (fun v u=>H' v u∧v∈X ω∧u∈Z ω))
        (ordinaryPhysicalGraph (F ω) (fun _ _=>False)) (Function.Embedding.inl:V↪V⊕U)
        (ordinaryBoundaryHubSet H' (Z ω) (X ω)) (fun i=>(ordinaryBoundaryRimSet Q' (X ω) i).image Sum.inl)
        (fun i=>(ordinaryBoundaryRowSet H' (X ω) (Z ω) i).image Sum.inr))),
    let parent:=fun ω (h:E ω)=>hdeep ω h (Q₀ ω) (H₀ ω) (hinputs ω h);
    let data:=fun ω (h:E ω)=>Classical.choice (parent ω h);
    let ν:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1);
    1-(e₀+4/(Fintype.card (V⊕U):ℝ)^q+1/(Fintype.card V:ℝ)^q)≤
      (μ.sigma (fun _=>ν)).probability (fun z=>∃hE:E z.1,
        OrdinaryFreshTriangleBoundaryEventInside (Q₀ z.1) (Q z.1) (F z.1) (H₀ z.1) (H z.1) (X z.1) (Z z.1)
          γ κ b B ε η ζ p εres εsup βe βh (data z.1 hE) z.2) := by
  obtain ⟨ε,η,ζ,hε,hη,hζ,hmain⟩:=ordinary_adaptive_fresh_from_deep_parent_event γ κ b B hγ hκ hb hB
  refine ⟨ε,η,ζ,hε,hη,hζ,?_⟩
  intro p hp hp1 q εres εsup βe βh hres hsup hβe hβh
  obtain ⟨N,hN⟩:=hmain p hp hp1 (2*p) (by positivity) q εres εsup βe βh hres hsup hβe hβh
  refine ⟨N,?_⟩
  intro V U Ω Γ Color _ _ _ _ _ _ _ hn hu μ E e₀ hE P Q₀ F H₀ X Z π d s j raw
    pR pH density tR tH Ledit Q H endpointWeight κe pParent Lconf δend εcount tend Kscale hinputs hdeep parent data ν
  have hh:=hN V U Ω Γ Color hn hu μ E e₀ hE P Q₀ F H₀ X Z π d s j raw pR pH density tR tH Ledit
    endpointWeight κe pParent Lconf δend εcount tend Kscale hinputs hdeep
  exact ordinary_fresh_inside_bundle_event (μ.sigma (fun _=>ν)) E _ Q₀ Q F H₀ H X Z
    γ κ b B ε η ζ p εres εsup βe βh data hh
end Oberwolfach
