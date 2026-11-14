module

public import Oberwolfach.OrdinaryNonrootCoverNumericInputs

@[expose] public section
/-! The original nonroot numerical bounds persist when both deeper
    blocking sets are replaced by smaller subsets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_nonroot_numeric_inputs_smaller_deep
    (F:SimpleGraph V) (I T T':Finset V) (B W W':Finset U) (n₀ d:ℕ)
    (ω a ρ θ aLoad ζlimit ε δcut ζcut εcut pH εR εH Ledit href:ℝ)
    (hTT:T'⊆T) (hWW:W'⊆W)
    (h:OrdinaryNonrootNumericInputs F I T B W n₀ d ω a ρ θ aLoad ζlimit ε δcut ζcut εcut pH εR εH Ledit href):
    OrdinaryNonrootNumericInputs F I T' B W' n₀ d ω a ρ θ aLoad ζlimit ε δcut ζcut εcut pH εR εH Ledit href :=by
  dsimp only [OrdinaryNonrootNumericInputs] at h ⊢
  rcases h with ⟨hTI,hWB,hn,hIpos,hBpos,hωI,hBI,hTsize,hWsize,hδp,hζp,hhp,hhrim,
    herror,hcol,hrow,hcutbudget,hI,hT,hW,hL,hLsmall,hF,hedit,hbudgetI,hbudgetB,hnlarge⟩
  have hTcard:(T'.card:ℝ)≤T.card:=by exact_mod_cast Finset.card_le_card hTT
  have hWcard:(W'.card:ℝ)≤W.card:=by exact_mod_cast Finset.card_le_card hWW
  refine ⟨hTT.trans hTI,hWW.trans hWB,hn,hIpos,hBpos,hωI,hBI,?_,?_,hδp,hζp,hhp,hhrim,
    herror,hcol,hrow,hcutbudget,hI,?_,?_,hL,hLsmall,hF,hedit,hbudgetI,hbudgetB,hnlarge⟩
  · exact hTcard.trans hTsize
  · exact hWcard.trans hWsize
  · exact hTcard.trans hT
  · linarith only [hWcard,hW]
end Oberwolfach
