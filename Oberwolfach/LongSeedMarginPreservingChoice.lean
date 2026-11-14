module

public import Oberwolfach.LongOriginalSeedMatchingMargin

@[expose] public section
/-! Preserve an arbitrary early-selected seed payload while imposing the
large even length and matching margin. This isolates the arithmetic from
large dependent weight statements. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_seed_margin_preserving_choice
    (L:ℕ) (αRef βList:ℝ) (hαRef:0<αRef) (hβList:0<βList)
    (Payload:ℕ→Prop)
    (hselect:∀L₀:ℕ,∃m:ℕ,7≤m ∧ L₀≤m ∧ Even (m+1) ∧ Payload m):
    ∃m r k₀:ℕ,7≤m ∧ L≤m ∧ Even (m+1) ∧ 2≤r ∧ m=r+4 ∧
      r+4+1=(k₀+2)*2 ∧ successorCycleRatio k₀+αRef/2≤1/2+αRef ∧
      1/(100*((r+4:ℕ):ℝ))≤βList/16 ∧ Payload m :=by
  obtain ⟨N,hN,hmargin⟩:=long_original_seed_matching_margin αRef βList hαRef hβList
  obtain ⟨m,hm,hlarge,heven,hpayload⟩:=hselect (max L N)
  obtain ⟨r,k₀,hr,hrm,hlen,hcycle,htrim⟩:=hmargin m (by omega) hm heven
  exact ⟨m,r,k₀,hm,by omega,heven,hr,hrm,hlen,hcycle,htrim,hpayload⟩
end Oberwolfach
