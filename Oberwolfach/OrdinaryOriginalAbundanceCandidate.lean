module

public import Oberwolfach.OrdinaryAbundanceCandidateCutoff

@[expose] public section
/-! Connect the original common r-cycle abundance assumption to the weaker
    candidate condition used by the generalized matching construction. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_original_abundance_gives_candidate
    {n:ℕ} (hn:0<n) {U:Type} [Fintype U]
    (F:U→SimpleGraph (Fin n)) (r K:ℕ) (hr:3≤r) (hrK:r≤K)
    (β:ℝ) (hβ:1/(2*(K:ℝ))≤β)
    (hfreq:∀w,β*n≤((Finset.univ.filter (fun v=>Fintype.card ((F w).connectedComponentMk v)=r)).card:ℝ)):
    ∃i₀:Fin K,i₀.val+1=r ∧ ∀w,i₀∈factorShortCandidates (F w) K:=by
  let i₀:Fin K:=⟨r-1,by omega⟩
  have hi:i₀.val+1=r:=by dsimp [i₀];omega
  refine ⟨i₀,hi,?_⟩
  apply ordinary_specified_abundance_is_candidate hn F K i₀ β hβ
  simpa only [hi] using hfreq
end Oberwolfach
