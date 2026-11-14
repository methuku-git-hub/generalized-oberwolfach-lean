module

public import Oberwolfach.MarkedCutSpokeChanges
public import Oberwolfach.BipartiteLargeCutEmbedding

@[expose] public section
/-! Translating the retained cut-family inequalities to normalized large cuts. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_cut_families_spoke_large_cut
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (α p k tstar ζ δ h:ℝ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hn:0<Fintype.card V) (hu:0<Fintype.card U)
    (hδ:2*δ≤tstar/8) (hh:h≤tstar/8-ζ)
    (hc:MarkedCutFamiliesWithSpokes P π d α p k tstar ζ σ H):
    ∀ mark,BipartiteLargeCut (relationMultiplicity (H mark)) δ h:=by
  intro mark S T hST
  have hlarge:1-tstar/8<(S.card:ℝ)/Fintype.card V+(T.card:ℝ)/Fintype.card U:=by linarith
  have hcut:=hc.1 mark S T hlarge
  rw [bipartiteLargeCut_sum_restrict,bipartite_normalized_cut_scale hn hu]
  apply le_trans (mul_le_mul_of_nonneg_right hh (by positivity))
  have heq:(fun v u=>if H mark v u then (1:ℕ) else 0)=relationMultiplicity (H mark):=by
    funext v u
    by_cases hv:H mark v u <;> simp [relationMultiplicity,hv]
  rw [←heq]
  exact hcut

theorem marked_cut_families_rim_large_cut
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (α p k tstar ζ δ h:ℝ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hn:0<Fintype.card V) (hδα:δ≤α/32) (hδp:δ≤p/32) (hδk:δ≤k/32)
    (hhp:h≤α*p/4) (hhk:h≤α*k/4)
    (hc:MarkedCutFamiliesWithSpokes P π d α p k tstar ζ σ H):
    ∀ mark,BipartiteLargeCut (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark) δ h:=by
  intro mark S T hST
  have hn':(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
  rw [←add_div] at hST
  have hlarge:(1-2*δ)*Fintype.card V<(S.card:ℝ)+T.card:=(lt_div_iff₀ hn').mp hST
  have hδmark:δ≤(if mark then k else p)/32:=by
    cases mark
    · simpa using hδp
    · simpa using hδk
  have hhmark:h≤α*(if mark then k else p)/4:=by
    cases mark
    · simpa using hhp
    · simpa using hhk
  have hcut:=hc.2 mark δ hδα hδmark S T hlarge
  rw [bipartiteLargeCut_sum_restrict,bipartite_normalized_cut_scale hn hn]
  have hscale:min ((Fintype.card V:ℝ)*S.card) ((Fintype.card V:ℝ)*T.card)=
      (Fintype.card V:ℝ)*min (S.card:ℝ) T.card:=by
    rw [mul_min_of_nonneg _ _ hn'.le]
  rw [hscale]
  have hfactor:0≤(Fintype.card V:ℝ)*min (S.card:ℝ) T.card:=mul_nonneg hn'.le (le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hcoeff:=mul_le_mul_of_nonneg_right hhmark hfactor
  change _≤(matrixCut _ S T:ℝ)
  nlinarith only [hcoeff,hcut]
end Oberwolfach
