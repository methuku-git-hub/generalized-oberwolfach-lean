module

public import Oberwolfach.OrdinaryCandidateClassReservation

@[expose] public section
/-! The originally specified abundant length is an eligible short candidate
    once the cutoff K is chosen sufficiently large in terms of its abundance. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_specified_abundance_is_candidate {n:ℕ} (hn:0<n)
    {U:Type} [Fintype U] (F:U→SimpleGraph (Fin n))
    (K:ℕ) (i₀:Fin K) (β:ℝ) (hβ:1/(2*(K:ℝ))≤β)
    (hfreq:∀w,β*n≤((Finset.univ.filter (fun v=>Fintype.card ((F w).connectedComponentMk v)=i₀.val+1)).card:ℝ)):
    ∀w,i₀∈factorShortCandidates (F w) K:=by
  intro w
  have hnR:0<(n:ℝ):=by exact_mod_cast hn
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  exact hβ.trans ((le_div_iff₀ hnR).2 (hfreq w))
end Oberwolfach
