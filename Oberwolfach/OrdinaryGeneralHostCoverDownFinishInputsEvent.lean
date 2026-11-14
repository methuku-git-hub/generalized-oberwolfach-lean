module

public import Oberwolfach.OrdinaryGeneralHostCoverDownSampleEvent
public import Oberwolfach.OrdinaryGeneralFinishSampleInputs

@[expose] public section
/-! Conditional high-probability packing and sparse cleanup on the same
sample, with the packing constructed before cleanup. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
set_option synthInstance.maxSize 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_general_host_coverdown_on_finish_inputs_event (m:ℕ) (hm:3≤m) (α:ℝ) (hα:0<α):
    ∃N:ℕ,∀k:ℕ,N≤k→∀ω β bminus bplus hpack δ:ℝ,
      0<ω→0<β→0<bminus→0<bplus→0<hpack→0<δ→δ<1/4→
    ∃εstar:ℝ,0<εstar ∧ ∀p βe βh ν cap:ℝ,0<p→0<βe→0<βh→0<ν→0<cap→
    ∃τ:ℝ,0<τ ∧ τ≤cap ∧ ∀L:ℝ,0≤L→∃η:ℝ,0<η ∧ ∃n₀:ℕ,
    ∀(V U Γ Color Ω:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [Fintype Ω]
      [DecidableEq V] [DecidableEq U],n₀≤Fintype.card V→
    ∀(μ:FiniteLaw Ω) (E:Ω→Prop) (e:ℝ),1-e≤μ.probability E→
    ∀(P Q F:Ω→SimpleGraph V) (H:Ω→V→U→Prop) (π:Equiv.Perm V) (d:ℕ)
      (X:Ω→Finset V) (Z:Ω→Finset U) (s:U→Color→ℝ) (j:Color)
      (raw:Ω→RawWheelOutcome V U Γ Color) (σ:Ω→Sym2 (V⊕U)→Bool)
      (β₀ h ε₀ ξ ζ ε b c pR pH density tR tH Ledit:ℝ),
    hpack≤h-ξ-ζ→
    (∀a,E a→OrdinaryPackingCleanupSampleInputs (m+1) (by omega) k d α ω β₀ β bminus bplus h δ ε₀ εstar η ξ ζ p ε b c
      pR pH density tR tH Ledit βe βh L (P a) (Q a) (F a) (H a) π (X a) (Z a) s j (raw a) (σ a))→
    ∀(Kcap Dmax:ℕ) (κ ζf εsupport:ℝ),
    (∀a,E a→OrdinaryGeneralFinishSampleInputs m d (P a) (Q a) (F a) (H a) π (X a) (Z a) (σ a)
      pR pH p density tR tH Ledit βe βh (τ*Fintype.card (V⊕U)) (ν*Fintype.card (V⊕U)) κ ζf εsupport Dmax Kcap L s j (raw a))→
    1-e≤μ.probability (fun a=>E a ∧
      OrdinaryGeneralHostCoverDownResult (Q a) (F a) (H a) (X a) (Z a) (m+1)
        (ν*Fintype.card (V⊕U)+2*((2*p)*Fintype.card (V⊕U))+((3*(Kcap+Dmax)+Dmax*(m+1):ℕ):ℝ))):=by
  obtain ⟨N,hN⟩:=ordinary_general_host_coverdown_on_sample_event_capped m hm α hα
  refine ⟨N,?_⟩
  intro k hk ω β bminus bplus hpack δ hω hβ hbm hbp hh hδ hδ1
  obtain ⟨εstar,hε,hmain⟩:=hN k hk ω β bminus bplus hpack δ hω hβ hbm hbp hh hδ hδ1
  refine ⟨εstar,hε,?_⟩
  intro p βe βh ν cap hp hβe hβh hν hcap
  obtain ⟨τ,hτ,hτcap,hmain⟩:=hmain p βe βh ν cap hp hβe hβh hν hcap
  refine ⟨τ,hτ,hτcap,?_⟩
  intro L hL
  obtain ⟨η,hη,n₀,hmain⟩:=hmain L hL
  refine ⟨η,hη,n₀,?_⟩
  intro V U Γ Color Ω _ _ _ _ _ _ _ hn μ E e hE P Q F H π d X Z s j raw σ
    β₀ h ε₀ ξ ζ ε b c pR pH density tR tH Ledit hcut hinputs Kcap Dmax κ ζf εsupport hdata
  apply hmain V U Γ Color Ω hn μ E e hE P Q F H π d X Z s j raw σ
    β₀ h ε₀ ξ ζ ε b c pR pH density tR tH Ledit hcut hinputs Kcap Dmax (2*p)
  intro a ha R M C Q₁ H₁ K Q₂ H₂
  exact ordinary_general_finish_from_sample_inputs m d hm (P a) (Q a) (F a) (H a) π (X a) (Z a) (σ a)
    pR pH p density tR tH Ledit βe βh (τ*Fintype.card (V⊕U)) (ν*Fintype.card (V⊕U)) κ ζf εsupport Dmax Kcap L s j (raw a)
    (hdata a ha) M K
end Oberwolfach
