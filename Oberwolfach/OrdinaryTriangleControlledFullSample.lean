module

public import Oberwolfach.OrdinaryPackingCleanupSameSampleCapped
public import Oberwolfach.OrdinaryTriangleControlledSameSample

@[expose] public section
/-! The near-balance packing, sparse cleanup and triangle finish combine
into one controlled level step on the same high-probability sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
set_option synthInstance.maxSize 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_controlled_level_on_sample_event (α:ℝ) (hα:0<α):
    ∃N:ℕ,∀k:ℕ,N≤k→∀ω β bminus bplus hpack δ:ℝ,
      0<ω→0<β→0<bminus→0<bplus→0<hpack→0<δ→δ<1/4→
    ∃εstar:ℝ,0<εstar ∧ ∀p βe βh ν cap:ℝ,0<p→0<βe→0<βh→0<ν→0<cap→
    ∃τ:ℝ,0<τ ∧ τ≤cap ∧ ∀L:ℝ,0≤L→∃η:ℝ,0<η ∧ ∃n₀:ℕ,
    ∀(V U Γ Color Ω:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [Fintype Ω]
      [DecidableEq V] [DecidableEq U],n₀≤Fintype.card V→
    ∀(μ:FiniteLaw Ω) (E:Ω→Prop) (e:ℝ),1-e≤μ.probability E→
    ∀(P Q F Qfactor:Ω→SimpleGraph V) (H Hfactor:Ω→V→U→Prop) (π:Equiv.Perm V) (d:ℕ)
      (X:Ω→Finset V) (Z:Ω→Finset U) (s:U→Color→ℝ) (j:Color)
      (raw:Ω→RawWheelOutcome V U Γ Color) (σ:Ω→Sym2 (V⊕U)→Bool)
      (β₀ h ε₀ ξ ζ ε b c pR pH density tR tH Ledit:ℝ)
      (γ κ bf Bf εf ηf ζf εsup:ℝ),
    hpack≤h-ξ-ζ→
    (∀a,E a→OrdinaryPackingCleanupSampleInputs 3 (by omega) k d α ω β₀ β bminus bplus h δ ε₀ εstar η ξ ζ p ε b c
      pR pH density tR tH Ledit βe βh L (P a) (Q a) (F a) (H a) π (X a) (Z a) s j (raw a) (σ a))→
    (∀a,E a→OrdinaryTriangleFinishSampleInputs (Q a) (Qfactor a) (F a) (H a) (Hfactor a) (X a) (Z a) (σ a)
      γ κ bf Bf εf ηf ζf p εsup τ ν)→
    1-e≤μ.probability (fun a=>E a ∧ OrdinaryTriangleControlledCoverDownResult (Q a) (H a) (X a) (Z a)
      ((ν+4*p)*Fintype.card (V⊕U))):=by
  obtain ⟨N,hN⟩:=ordinary_packing_cleanup_on_sample_event_capped 3 (by omega) α hα
  refine ⟨N,?_⟩
  intro k hk ω β bminus bplus hpack δ hω hβ hbm hbp hh hδ hδ1
  obtain ⟨εstar,hε,hpack⟩:=hN k hk ω β bminus bplus hpack δ hω hβ hbm hbp hh hδ hδ1
  refine ⟨εstar,hε,?_⟩
  intro p βe βh ν cap hp hβe hβh hν hcap
  obtain ⟨τ,hτ,hτcap,hτrule⟩:=hpack p βe βh ν cap hp hβe hβh hν hcap
  refine ⟨τ,hτ,hτcap,?_⟩
  intro L hL
  obtain ⟨η,hη,n₀,hn₀⟩:=hτrule L hL
  refine ⟨η,hη,n₀,?_⟩
  intro V U Γ Color Ω _ _ _ _ _ _ _ hn μ E e hE P Q F Qfactor H Hfactor π d X Z s j raw σ
    β₀ h ε₀ ξ ζ ε b c pR pH density tR tH Ledit γ κ bf Bf εf ηf ζf εsup hcut hinput hfinish
  have hpackprob:1-e≤μ.probability (fun a=>E a∧OrdinaryPackingCleanupOutcome (Q a) (F a) (H a) (X a) (Z a) (σ a) τ ν):=
    hn₀ V U Γ Color Ω hn μ E e hE P Q F H π d X Z s j raw σ β₀ h ε₀ ξ ζ ε b c pR pH density tR tH Ledit hcut hinput
  have hfinishprob:=ordinary_packing_cleanup_finish_event μ E e Q Qfactor F H Hfactor X Z σ
    γ κ bf Bf εf ηf ζf p εsup τ ν hpackprob hfinish
  exact ordinary_triangle_controlled_cover_down_same_sample μ E e Q F H X Z σ p τ ν hfinishprob
    (fun a ha=>(hinput a ha).balanced) (fun a ha=>(hinput a ha).divisible)
end Oberwolfach
