module

public import Oberwolfach.MarkedEndpointBlockBounds

@[expose] public section

/-! Parameter order for the five endpoint blocks. The relative tolerance
is fixed before the permutation radius; only the order threshold depends
on that radius. No endpoint degree or cut is postulated here. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach

theorem marked_endpoint_block_numeric_threshold (p₀ a eta : ℝ)
    (hp₀ : 0<p₀) (hp₀1 : p₀≤1) (ha : 0<a) (heta : 0<eta)
    (hetaSmall : eta≤p₀*a/8) :
    ∃ eps e : ℝ,0<eps ∧ 0<e ∧ ∀ d : ℕ,∃ n₀ : ℕ,∀ n : ℕ,n₀≤n →
      ∀ L Y : ℕ,a*n≤(L:ℝ) → a*n≤(Y:ℝ) → (Y:ℝ)≤n →
      ∀ p : ℝ,p₀≤p → p≤1 →
      (2*(eps*n)≤e*L) ∧ (2*(eps*n)≤e*Y) ∧
      e≤p^2*eta/24 ∧ ((6*d+1:ℕ):ℝ)≤p^2*eta^2*Y/8 ∧
      (p₀*a/2)*n≤(p-e)*L ∧ (p₀*a/2)*n≤(p-e)*Y ∧
      eta*Y≤eta*n ∧ p₀/2≤p/2 ∧
      2*(eta*n)+(2*(2*(3*d)+1):ℕ)≤(p₀*a/2)*n ∧
      (2*(2*(3*d)+1):ℕ)<(p₀/2)*(eta*n) := by
  let e := min (p₀/4) (p₀^2*eta/48)
  have he : 0<e := by dsimp [e];positivity
  let eps := e*a/4
  have heps : 0<eps := by dsimp [eps];positivity
  have hep : e≤p₀/4 := min_le_left _ _
  have heeta : e≤p₀^2*eta/48 := min_le_right _ _
  refine ⟨eps,e,heps,he,?_⟩
  intro d
  let B : ℝ := 6*d+1
  obtain ⟨n₀,hn₀⟩ := exists_nat_gt (max 1 (max (8*B/(p₀^2*eta^2*a))
    (max (8*B/(p₀*a)) (4*B/(p₀*eta)))))
  refine ⟨n₀,?_⟩
  intro n hn L Y hL hY hYn p hpp hp1
  have hn' : (n₀:ℝ)≤n := Nat.cast_le.mpr hn
  have hnall := hn₀.trans_le hn'
  have hnpos : (0:ℝ)<n := by have hh:=(le_max_left _ _).trans_lt hnall;linarith
  have hcutN : 8*B<(n:ℝ)*(p₀^2*eta^2*a) := by
    apply (div_lt_iff₀ (by positivity)).mp
    exact ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hnall
  have hdegN : 8*B<(n:ℝ)*(p₀*a) := by
    apply (div_lt_iff₀ (by positivity)).mp
    exact ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans_lt hnall
  have hmatchN : 4*B<(n:ℝ)*(p₀*eta) := by
    apply (div_lt_iff₀ (by positivity)).mp
    exact ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans_lt hnall
  have hp : 0<p := hp₀.trans_le hpp
  have hp2 : p₀^2≤p^2 := by nlinarith only [hp₀,hpp]
  have hlower : p₀/2≤p-e := by linarith only [hep,hpp,hp₀]
  have hnorm (Z : ℕ) (hZ : a*n≤(Z:ℝ)) : 2*(eps*n)≤e*Z := by
    have hh := mul_le_mul_of_nonneg_left hZ he.le
    have hn0 : 0≤e*a*n := by positivity
    dsimp [eps]
    nlinarith only [hh,hn0]
  have hd (Z : ℕ) (hZ : a*n≤(Z:ℝ)) : (p₀*a/2)*n≤(p-e)*Z := by
    have h₁ := mul_le_mul_of_nonneg_left hZ (by positivity : 0≤p₀/2)
    have h₂ := mul_le_mul_of_nonneg_right hlower (Nat.cast_nonneg Z)
    nlinarith only [h₁,h₂]
  refine ⟨hnorm L hL,hnorm Y hY,?_,?_,hd L hL,hd Y hY,?_,?_,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_right hp2 (show 0≤eta/48 by positivity)
    have hnn : 0≤p^2*eta := by positivity
    nlinarith only [heeta,hh,hnn]
  · have h₁ := mul_le_mul_of_nonneg_left hY (show 0≤p₀^2*eta^2 by positivity)
    have h₂ := mul_le_mul_of_nonneg_right hp2 (show 0≤eta^2*Y by positivity)
    dsimp [B] at hcutN
    push_cast
    nlinarith only [hcutN,h₁,h₂]
  · exact mul_le_mul_of_nonneg_left hYn heta.le
  · linarith only [hpp]
  · have hh := mul_le_mul_of_nonneg_right hetaSmall hnpos.le
    dsimp [B] at hdegN
    push_cast
    nlinarith only [hdegN,hh]
  · dsimp [B] at hmatchN
    push_cast
    nlinarith only [hmatchN]

end Oberwolfach
