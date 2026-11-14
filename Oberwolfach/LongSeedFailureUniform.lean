module

public import Oberwolfach.LongSeedEvents
public import Oberwolfach.MixedSeedFailureMargin

@[expose] public section
/-! A common threshold for the named fixed-family concentration event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach

theorem eventually_named_mixed_seed_failure_below
    (d m K:ℕ) (ℓ:Fin K→ℕ) (BM:ℝ) (BO:Fin K→ℝ) (t δ:ℝ)
    (hBM:0<BM) (hBO:∀i,0<BO i) (ht:0<t) (hδ:0<δ):
    ∃N:ℕ,∀n:ℕ,N≤n→∀U:Type,[Fintype U]→Fintype.card U≤n→
      mixedSeedFailureBound (Fin n) U d m K ℓ BM BO t<δ :=by
  obtain ⟨N,hN⟩:=eventually_mixed_seed_failure_below d m K ℓ BM BO t δ hBM hBO ht hδ
  refine ⟨N,?_⟩
  intro n hn U _ hu
  simpa only [mixedSeedFailureBound,Fintype.card_fin] using hN n hn U hu
end Oberwolfach
