module

public import Oberwolfach.RawOrdinarySpokeCuts
public import Oberwolfach.RawPhysicalCuts

@[expose] public section

/-! One simultaneous large-cut event for the ordinary spoke graph and the
oriented admissible physical sample. Constants precede both the conflict
degree and interval length; the realised experiment is unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_reference_large_cuts
    (α pstar ω : ℝ) (hα : 0<α) (hα1 : α≤1/2)
    (hpstar : 0<pstar) (hpstar1 : pstar≤1) (hω : 0<ω) :
    ∃ δ h : ℝ,0<δ ∧ δ<1/4 ∧ 0<h ∧
    ∀ L : ℝ,0≤L → ∀ d q₀ : ℕ,∀ hd : 2≤d,∃ N : ℕ,
    ∀ (V U Γ Color : Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U],
      N≤Fintype.card V → ω*Fintype.card V≤(Fintype.card U:ℝ) → Fintype.card U≤Fintype.card V →
    ∀ P F : SimpleGraph V,(∀ v,(1/2+α)*Fintype.card V≤(P.degree v:ℝ)) →
      (∀ v,(F.degree v:ℝ)≤L) →
    ∀ (π : Equiv.Perm V),(∀ x k,0<k → k<2*d+1 → (π^k) x≠x) →
    ∀ (pR pH : ℝ) (hR : 0≤pR) (hR1 : pR≤1),pstar≤pR → pstar≤pH →
    ∀ (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (j : Color),(∀ u,s u j=pH) →
    let μ := (FiniteLaw.pi (rawWheelLaw (fun _ : Sym2 V=>pR) (fun _=>hR) (fun _=>hR1)
      d hd q hq hQ s hs hS)).prod (FiniteLaw.pi (fun _ : Sym2 V=>FiniteLaw.fairCoin))
    1-1/(Fintype.card V:ℝ)^q₀≤μ.probability (fun z=>
      (∀ (X : Finset V) (Y : Finset U),
        1-2*δ<(X.card:ℝ)/Fintype.card V+(Y.card:ℝ)/Fintype.card U →
        2*h*min ((Fintype.card U:ℝ)*X.card) ((Fintype.card V:ℝ)*Y.card)≤
          (bipartiteMatrixCut (fun v u=>if rawWheelSpokes π d z.1 j v u then 1 else 0) X Y:ℝ)) ∧
      (∀ S T : Finset V,
        1-2*δ<(S.card:ℝ)/Fintype.card V+(T.card:ℝ)/Fintype.card V →
        2*h*min ((Fintype.card V:ℝ)*S.card) ((Fintype.card V:ℝ)*T.card)≤
          (matrixCut (sampledOrientation ((rawWheelGraph P z.1)\F) z.2) S T:ℝ))) := by
  let δ : ℝ := min (α/64) (pstar/512)
  let h : ℝ := α*pstar/256
  refine ⟨δ,h,lt_min (by positivity) (by positivity),?_,by dsimp [h];positivity,?_⟩
  · have hh := min_le_left (α/64) (pstar/512)
    dsimp [δ]
    linarith only [hh,hα1]
  intro L hL d q₀ hd
  obtain ⟨N₁,hN₁⟩ := rawWheelSpokeCuts_uniform_probability pstar ω hpstar hpstar1 hω d (q₀+1) hd
  obtain ⟨N₂,hN₂⟩ := rawWheel_physical_large_cuts (α/2) pstar (by positivity) (by linarith) hpstar (q₀+1)
  obtain ⟨N₃,hN₃⟩ := exists_nat_ge (2*L/α)
  refine ⟨max 2 (max N₁ (max N₂ N₃)),?_⟩
  intro V U Γ Color _ _ _ _ _ _ hnN hmlo hmhi P F hP hF π hnoshort pR pH hR hR1 hRlo hHlo q hq hQ s hs hS j hj
  let n := Fintype.card V
  have hn : 0<n := by dsimp [n];omega
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hLn : L≤α*n/2 := by
    have hh : 2*L/α≤(n:ℝ) := hN₃.trans (by exact_mod_cast (show N₃≤n by dsimp [n];omega))
    have hh' := (div_le_iff₀ hα).mp hh
    linarith only [hh']
  have hPadm (v : V) : (1/2+α/2)*Fintype.card V≤((P\F).degree v:ℝ) := by
    have hh := graph_degree_le_sdiff_add P F v
    have hhR : (P.degree v:ℝ)≤((P\F).degree v:ℝ)+(F.degree v:ℝ) := by exact_mod_cast hh
    linarith only [hP v,hF v,hLn,hhR]
  let ν := FiniteLaw.pi (fun _ : Sym2 V=>FiniteLaw.fairCoin)
  let μ₀ := FiniteLaw.pi (rawWheelLaw (fun _ : Sym2 V=>pR) (fun _=>hR) (fun _=>hR1)
      d hd q hq hQ s hs hS)
  let E₁ := fun σ : RawWheelOutcome V U Γ Color=>∀ (X : Finset V) (Y : Finset U),
      1-pstar/8<(X.card:ℝ)/Fintype.card V+(Y.card:ℝ)/Fintype.card U →
      pstar/8*min ((Fintype.card U:ℝ)*X.card) ((Fintype.card V:ℝ)*Y.card)≤
        (bipartiteMatrixCut (fun v u=>if rawWheelSpokes π d σ j v u then 1 else 0) X Y:ℝ)
  have hspoke : 1-1/(n:ℝ)^(q₀+1)≤(μ₀.prod ν).probability (fun z=>E₁ z.1) := by
    rw [finiteLaw_prod_first_probability]
    exact hN₁ V U Γ Color (by omega) hmlo hmhi π (fun _=>pR) (fun _=>hR) (fun _=>hR1)
      q hq hQ s hs hS j hnoshort pH hHlo hj
  have hphysical := hN₂ V U Γ Color (by omega) (P\F)
    (by intro v;simpa only [← SimpleGraph.ncard_neighborSet,← Nat.card_eq_fintype_card] using hPadm v)
    pR hR hR1 hRlo d hd q hq hQ s hs hS
  have hjoint := finiteLaw_good_intersection (μ₀.prod ν) (fun z=>E₁ z.1) _
    (1/(n:ℝ)^(q₀+1)) hphysical
  have hbase := (sub_le_sub_right hspoke (1/(n:ℝ)^(q₀+1))).trans hjoint
  have hsum := scaled_inverse_power_le n q₀ hn 2 (by exact_mod_cast (show 2≤n by dsimp [n];omega))
  have hbound : 1-1/(n:ℝ)^q₀≤(1-1/(n:ℝ)^(q₀+1))-1/(n:ℝ)^(q₀+1) := by
    convert sub_le_sub_left hsum 1 using 1 <;> ring
  apply (hbound.trans hbase).trans
  apply finiteLaw_probability_mono
  intro z hz
  constructor
  · intro X Y hlarge
    have hδ : 2*δ≤pstar/8 := by
      have hh := min_le_right (α/64) (pstar/512)
      dsimp [δ]
      linarith only [hh,hpstar]
    have hh := hz.1 X Y (by linarith only [hlarge,hδ])
    have hc : 2*h≤pstar/8 := by
      have ha := mul_le_mul_of_nonneg_right hα1 hpstar.le
      dsimp [h]
      linarith only [ha,hpstar]
    exact (mul_le_mul_of_nonneg_right hc (by positivity)).trans hh
  · intro S T hlarge
    have hlarge' : (1-2*min ((α/2)/32) (pstar/512))*Fintype.card V<(S.card:ℝ)+T.card := by
      have hh := mul_lt_mul_of_pos_right hlarge hn0
      have heq : ((S.card:ℝ)/n+(T.card:ℝ)/n)*n=(S.card:ℝ)+T.card := by field_simp
      change (1-2*δ)*(n:ℝ)<((S.card:ℝ)/n+(T.card:ℝ)/n)*n at hh
      rw [heq] at hh
      convert hh using 1 <;> dsimp [δ,n] <;> ring
    have hh := hz.2 S T hlarge'
    rw [rawWheelGraph_sdiff] at hh
    rw [← mul_min_of_nonneg _ _ hn0.le]
    convert hh using 1 <;> dsimp [h,n] <;> ring

end Oberwolfach
