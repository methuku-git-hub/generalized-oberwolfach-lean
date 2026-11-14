module

public import Oberwolfach.OrdinaryTriangleInputsFromPreLevel
public import Oberwolfach.OrdinaryTriangleControlledFullSampleInside

@[expose] public section
/-! A prior event carrying the explicit same-sample reference, fresh-factor
and cleanup data yields a controlled triangle wheel level on that event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3500000
set_option synthInstance.maxSize 8192
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_controlled_level_from_prelevel_event (α:ℝ) (hα:0<α):
    ∃N:ℕ,∀k:ℕ,N≤k→∀ω β bminus bplus hpack δ:ℝ,
      0<ω→0<β→0<bminus→0<bplus→0<hpack→0<δ→δ<1/4→
    ∃εstar:ℝ,0<εstar ∧ ∀p βe βh ν cap:ℝ,0<p→0<βe→0<βh→0<ν→0<cap→
    ∃τ:ℝ,0<τ ∧ τ≤cap ∧ ∀L:ℝ,0≤L→∃η:ℝ,0<η ∧ ∃n₀:ℕ,
    ∀(V U Γ Color Ω:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [Fintype Ω]
      [LinearOrder V] [DecidableEq U],n₀≤Fintype.card V→
    ∀(μ:FiniteLaw Ω) (E:Ω→Prop) (e₀:ℝ),1-e₀≤μ.probability E→
    ∀(P Q Qfactor F:Ω→SimpleGraph V) (H Hfactor:Ω→V→U→Prop) (π:Equiv.Perm V) (d:ℕ)
      (X:Ω→Finset V) (Z:Ω→Finset U) (s:U→Color→ℝ) (j:Color)
      (raw:Ω→RawWheelOutcome V U Γ Color) (coins:Ω→Sym2 V→Bool) (σ:Ω→Sym2 (V⊕U)→Bool)
      (βsource βparent hOrig ζedit εsource εparent ξ ζreserve εreserve pR pH density tR tH e Ledit:ℝ)
      (γ κ bf Bf εf ηf ζf εsupport:ℝ),
    hpack≤(hOrig-ζedit)-ξ-ζreserve→
    (∀z,E z→Nonempty (OrdinaryTrianglePreLevelData k d α ω βsource βparent β bminus bplus hOrig ζedit δ
      εsource εparent εstar η ξ ζreserve p εreserve pR pH density tR tH e Ledit βe βh L
      γ κ bf Bf εf ηf ζf εsupport τ ν (P z) (Q z) (Qfactor z) (F z) (H z) (Hfactor z) π (X z) (Z z) s j (raw z) (coins z) (σ z)))→
    1-e₀≤μ.probability (fun z=>E z ∧ OrdinaryTriangleControlledCoverDownResult (Q z) (H z) (X z) (Z z)
      ((ν+4*p)*Fintype.card (V⊕U))):=by
  obtain ⟨N,hN⟩:=ordinary_triangle_controlled_level_on_inside_sample_event α hα
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
  intro V U Γ Color Ω _ _ _ _ _ _ _ hn μ E e₀ hE P Q Qfactor F H Hfactor π d X Z s j raw coins σ
    βsource βparent hOrig ζedit εsource εparent ξ ζreserve εreserve pR pH density tR tH e Ledit
    γ κ bf Bf εf ηf ζf εsupport hcut hpre
  let pdata:=fun z (hz:E z)=>Classical.choice (hpre z hz)
  have hinputs:∀z,E z→OrdinaryPackingCleanupSampleInputs 3 (by omega) k d α ω βparent β bminus bplus
      (hOrig-ζedit) δ εparent εstar η ξ ζreserve p εreserve (e+tR+2*tH+3*Ledit) (e+tR+2*tH+3*Ledit)
      pR pH density tR tH Ledit βe βh L (P z) (Q z) (F z) (H z) π (X z) (Z z) s j (raw z) (σ z) := by
    intro z hz
    exact (ordinary_triangle_inputs_from_prelevel k d α ω βsource βparent β bminus bplus hOrig ζedit δ
      εsource εparent εstar η ξ ζreserve p εreserve pR pH density tR tH e Ledit βe βh L
      γ κ bf Bf εf ηf ζf εsupport τ ν (P z) (Q z) (Qfactor z) (F z) (H z) (Hfactor z) π (X z) (Z z)
      s j (raw z) (coins z) (σ z) (pdata z hz)).1
  have hfinish:∀z,E z→OrdinaryTriangleFinishSampleInputsInside (Q z) (Qfactor z) (F z) (H z) (Hfactor z) (X z) (Z z) (σ z)
      γ κ bf Bf εf ηf ζf p εsupport τ ν := by
    intro z hz
    exact (ordinary_triangle_inputs_from_prelevel k d α ω βsource βparent β bminus bplus hOrig ζedit δ
      εsource εparent εstar η ξ ζreserve p εreserve pR pH density tR tH e Ledit βe βh L
      γ κ bf Bf εf ηf ζf εsupport τ ν (P z) (Q z) (Qfactor z) (F z) (H z) (Hfactor z) π (X z) (Z z)
      s j (raw z) (coins z) (σ z) (pdata z hz)).2
  exact hmain V U Γ Color Ω hn μ E e₀ hE P Q F Qfactor H Hfactor π d X Z s j raw σ
    βparent (hOrig-ζedit) εparent ξ ζreserve εreserve (e+tR+2*tH+3*Ledit) (e+tR+2*tH+3*Ledit)
    pR pH density tR tH Ledit γ κ bf Bf εf ηf ζf εsupport hcut hinputs hfinish
end Oberwolfach
