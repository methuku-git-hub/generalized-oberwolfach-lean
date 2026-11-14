module

public import Oberwolfach.FactorClassAssignment

@[expose] public section
/-! The long-cycle abundance in the original long preparation statement
    implies its classifier hypothesis directly, for every factor. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_original_abundance_gives_class_none {n K:ℕ} (hn:0<n)
    {U:Type} [Fintype U] (F:U→SimpleGraph (Fin n))
    (hLong:∀w,(n:ℝ)/2≤((Finset.univ.filter (fun v=>K<Fintype.card ((F w).connectedComponentMk v))).card:ℝ)):
    ∀w,factorPreparationClass (F w) K=none:=by
  intro w
  have hnR:0<(n:ℝ):=by exact_mod_cast hn
  have hh:(1/2:ℝ)≤((Finset.univ.filter (fun v=>K<Fintype.card ((F w).connectedComponentMk v))).card:ℝ)/n:=by
    apply (le_div_iff₀ hnR).2
    linarith [hLong w]
  simp only [factorPreparationClass,hh,ite_true]
end Oberwolfach
