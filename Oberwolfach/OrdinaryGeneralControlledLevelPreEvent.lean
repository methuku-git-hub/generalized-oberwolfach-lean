module

public import Oberwolfach.OrdinaryGeneralPreLevelData
public import Oberwolfach.OrdinaryGeneralHostCoverDownFinishInputsEvent

@[expose] public section
/-! A prior carrying the explicit general-length reference, common profiles,
fresh pairing and numerical data yields the conflict-respecting wheel level
on that same outcome. The prior itself is not asserted unconditionally. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 10000000
set_option synthInstance.maxSize 16384
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_general_controlled_level_from_prelevel_event (m:ℕ) (hm:3≤m) (α:ℝ) (hα:0<α):
    ∃N:ℕ,∀k:ℕ,N≤k→∀ω β bminus bplus hpack δ:ℝ,
      0<ω→0<β→0<bminus→0<bplus→0<hpack→0<δ→δ<1/4→
    ∃εstar:ℝ,0<εstar ∧ ∀p βe βh ν cap:ℝ,0<p→0<βe→0<βh→0<ν→0<cap→
    ∃τ:ℝ,0<τ ∧ τ≤cap ∧ ∀L:ℝ,0≤L→∃η:ℝ,0<η ∧ ∃n₀:ℕ,
    ∀(V U Γ Color Ω:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [Fintype Ω]
      [LinearOrder V] [DecidableEq U],n₀≤Fintype.card V→
    ∀(μ:FiniteLaw Ω) (E:Ω→Prop) (e₀:ℝ),1-e₀≤μ.probability E→
    ∀(P Q F:Ω→SimpleGraph V) (H:Ω→V→U→Prop) (π:Equiv.Perm V) (d:ℕ)
      (X:Ω→Finset V) (Z:Ω→Finset U) (s:U→Color→ℝ) (j:Color)
      (raw:Ω→RawWheelOutcome V U Γ Color) (coins:Ω→Sym2 V→Bool) (σ:Ω→Sym2 (V⊕U)→Bool)
      (βsource βparent hOrig ζedit εsource εparent ξ ζreserve εreserve pR pH density tR tH e Ledit:ℝ)
      (Dmax Kcap:ℕ) (κ ζf εsupport:ℝ),
    hpack≤(hOrig-ζedit)-ξ-ζreserve→
    (∀z,E z→Nonempty (OrdinaryGeneralPreLevelData m k d hm α ω βsource βparent β bminus bplus hOrig ζedit δ
      εsource εparent εstar η ξ ζreserve p εreserve pR pH density tR tH e Ledit βe βh L τ ν κ ζf εsupport
      Dmax Kcap (P z) (Q z) (F z) (H z) π (X z) (Z z) s j (raw z) (coins z) (σ z)))→
    1-e₀≤μ.probability (fun z=>E z ∧ OrdinaryGeneralHostCoverDownResult (Q z) (F z) (H z) (X z) (Z z) (m+1)
      (ν*Fintype.card (V⊕U)+2*((2*p)*Fintype.card (V⊕U))+((3*(Kcap+Dmax)+Dmax*(m+1):ℕ):ℝ))):=by
  obtain ⟨N,hN⟩:=ordinary_general_host_coverdown_on_finish_inputs_event m hm α hα
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
  intro V U Γ Color Ω _ _ _ _ _ _ _ hn μ E e₀ hE P Q F H π d X Z s j raw coins σ
    βsource βparent hOrig ζedit εsource εparent ξ ζreserve εreserve pR pH density tR tH e Ledit Dmax Kcap κ ζf εsupport hcut hpre
  let pdata:=fun z (hz:E z)=>Classical.choice (hpre z hz)
  have hinputs:∀z,E z→OrdinaryPackingCleanupSampleInputs (m+1) (by omega) k d α ω βparent β bminus bplus
      (hOrig-ζedit) δ εparent εstar η ξ ζreserve p εreserve (e+tR+2*tH+3*Ledit) (e+tR+2*tH+3*Ledit)
      pR pH density tR tH Ledit βe βh L (P z) (Q z) (F z) (H z) π (X z) (Z z) s j (raw z) (σ z):=by
    intro z hz
    exact (ordinary_general_inputs_from_prelevel m k d hm α ω βsource βparent β bminus bplus hOrig ζedit δ
      εsource εparent εstar η ξ ζreserve p εreserve pR pH density tR tH e Ledit βe βh L τ ν κ ζf εsupport
      Dmax Kcap (P z) (Q z) (F z) (H z) π (X z) (Z z) s j (raw z) (coins z) (σ z) (pdata z hz)).1
  have hfinish:∀z,E z→OrdinaryGeneralFinishSampleInputs m d (P z) (Q z) (F z) (H z) π (X z) (Z z) (σ z)
      pR pH p density tR tH Ledit βe βh (τ*Fintype.card (V⊕U)) (ν*Fintype.card (V⊕U)) κ ζf εsupport Dmax Kcap L s j (raw z):=by
    intro z hz
    exact (pdata z hz).finish
  exact hmain V U Γ Color Ω hn μ E e₀ hE P Q F H π d X Z s j raw σ
    βparent (hOrig-ζedit) εparent ξ ζreserve εreserve (e+tR+2*tH+3*Ledit) (e+tR+2*tH+3*Ledit)
    pR pH density tR tH Ledit hcut hinputs Kcap Dmax κ ζf εsupport hfinish
end Oberwolfach
