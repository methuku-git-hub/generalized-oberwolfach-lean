module

public import Oberwolfach.RawPhysicalOrientation
public import Oberwolfach.SampledColourLargeCuts

@[expose] public section

/-! The physical large-cut event under the original raw wheel experiment,
with independent directions chosen for all physical edges in advance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem rawWheel_physical_large_cuts
    (α pstar : ℝ) (hα : 0<α) (hα1 : α≤1/2) (hpstar : 0<pstar) (q₀ : ℕ) :
    ∃ N : ℕ,∀ (V U Γ Color : Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U],
      N≤Fintype.card V →
    ∀ P : SimpleGraph V,(∀ v,(1/2+α)*Fintype.card V≤(P.degree v:ℝ)) →
    ∀ (p : ℝ) (hp : 0≤p) (hp1 : p≤1),pstar≤p →
    ∀ d : ℕ,∀ hd : 2≤d,
    ∀ (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g)),
    1-1/(Fintype.card V:ℝ)^q₀≤
      ((FiniteLaw.pi (rawWheelLaw (fun _ : Sym2 V=>p) (fun _=>hp) (fun _=>hp1)
        d hd q hq hQ s hs hS)).prod
        (FiniteLaw.pi (fun _ : Sym2 V=>FiniteLaw.fairCoin))).probability
        (fun z=>∀ S T : Finset V,
          (1-2*min (α/32) (pstar/512))*Fintype.card V<(S.card:ℝ)+T.card →
          (α*pstar/64)*Fintype.card V*min (S.card:ℝ) T.card≤
            (matrixCut (sampledOrientation (rawWheelGraph P z.1) z.2) S T:ℝ)) := by
  obtain ⟨N,hN⟩ := sampledColourOrientation_large_cuts α pstar hα hα1 hpstar 2 q₀
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn P hP p hp hp1 hplo d hd q hq hQ s hs hS
  rw [rawWheel_orientation_probability P p hp hp1 d hd q hq hQ s hs hS
    (fun M=>∀ S T : Finset V,
      (1-2*min (α/32) (pstar/512))*Fintype.card V<(S.card:ℝ)+T.card →
      (α*pstar/64)*Fintype.card V*min (S.card:ℝ) T.card≤(matrixCut M S T:ℝ))]
  have hh := hN V hn P hP (retentionColourProbability p)
    (retentionColourProbability_nonneg p hp hp1) (retentionColourProbability_sum p)
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ
  exact hσ 0 (by simpa [retentionColourProbability] using hplo)

theorem graph_degree_le_sdiff_add
    {V : Type*} [Fintype V] (P F : SimpleGraph V) (v : V) :
    P.degree v≤(P\F).degree v+F.degree v := by
  simpa only [← SimpleGraph.card_neighborFinset_eq_degree,SimpleGraph.neighborFinset_sdiff] using
    (Finset.card_le_card_sdiff_add_card (s:=P.neighborFinset v) (t:=F.neighborFinset v))

theorem rawWheelGraph_sdiff
    {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U]
    (P F : SimpleGraph V) (σ : RawWheelOutcome V U Γ Color) :
    rawWheelGraph (P\F) σ=(rawWheelGraph P σ)\F := by
  ext x y
  simp only [rawWheelGraph,retainedGraph,SimpleGraph.sdiff_adj]
  tauto

end Oberwolfach
