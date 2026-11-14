module

public import Oberwolfach.OrdinaryProtectedPreparationStatement

@[expose] public section
/-! A positive abundant class forces the reserved cycle threshold to lie
    below the original theorem's threshold; no extra density premise is needed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_abundance_threshold_from_original
    (θ ρstar β:ℝ) (hρstar:0<ρstar) (hβ:0<β)
    (n D q rstar:ℕ) (hn:0<n)
    (hρlo:ρstar≤2*(q:ℝ)/(D:ℝ))
    (F:Fin q→SimpleGraph (Fin n))
    (hthreshold:∀w v,cycleThreshold (Fintype.card ((F w).connectedComponentMk v))≤θ)
    (habundance:∀w,β*n≤((Finset.univ.filter (fun v=>Fintype.card ((F w).connectedComponentMk v)=rstar)).card:ℝ)):
    cycleThreshold rstar≤θ := by
  have hq:0<q:=by
    by_contra h
    have hz:q=0:=by omega
    subst q
    simp only [Nat.cast_zero,mul_zero,zero_div] at hρlo
    linarith
  let w:Fin q:=⟨0,hq⟩
  have hnR:(0:ℝ)<n:=by exact_mod_cast hn
  have hcount:0<(Finset.univ.filter (fun v=>Fintype.card ((F w).connectedComponentMk v)=rstar)).card:=by
    have hh: (0:ℝ)<((Finset.univ.filter (fun v=>Fintype.card ((F w).connectedComponentMk v)=rstar)).card:ℝ):=
      (mul_pos hβ hnR).trans_le (habundance w)
    exact_mod_cast hh
  obtain ⟨v,hv⟩:=Finset.card_pos.mp hcount
  have hv':Fintype.card ((F w).connectedComponentMk v)=rstar:=(Finset.mem_filter.mp hv).2
  simpa only [hv'] using hthreshold w v
end Oberwolfach
