module

public import Oberwolfach.FactorClassAssignment

@[expose] public section
/-! The original long-cycle condition selects the long class for each
factor, for any finite or infinite index type. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_class_from_original_long_cycles
    {n K:ℕ} {U:Type} (hn:0<n) (F:U→SimpleGraph (Fin n))
    (hlong:∀u,(n:ℝ)/2≤((Finset.univ.filter (fun v=>K<Fintype.card ((F u).connectedComponentMk v))).card:ℝ)):
    ∀u,factorPreparationClass (F u) K=none :=by
  have hnR:0<(n:ℝ):=by exact_mod_cast hn
  intro u
  have hlong':(1/2:ℝ)≤((Finset.univ.filter (fun v=>K<Fintype.card ((F u).connectedComponentMk v))).card:ℝ)/n:=by
    apply (le_div_iff₀ hnR).2
    nlinarith [hlong u]
  simp only [factorPreparationClass,if_pos hlong']
end Oberwolfach
