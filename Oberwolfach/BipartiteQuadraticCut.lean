module

public import Oberwolfach.DirectedCutBounds

@[expose] public section

/-! A large-cut bound from minimum degrees and quadratic cut error, for
unequal bipartite parts. Every numerical margin is explicit. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def bipartiteMatrixCut {A B : Type*} (M : A → B → ℕ) (S : Finset A) (T : Finset B) : ℕ :=
  ∑ x∈S,∑ y∈T,M x y

theorem bipartiteMatrixCut_transpose {A B : Type*} (M : A → B → ℕ) (S : Finset A) (T : Finset B) :
    bipartiteMatrixCut M S T=bipartiteMatrixCut (fun y x=>M x y) T S := Finset.sum_comm

theorem bipartiteMatrixCut_row_lower {A B : Type*} [Fintype B]
    (M : A → B → ℕ) (hM : ∀ x y,M x y≤1) (S : Finset A) (T : Finset B) (d : ℝ)
    (hrow : ∀ x∈S,d≤((∑ y,M x y:ℕ):ℝ)) :
    (S.card:ℝ)*(d+T.card-Fintype.card B)≤(bipartiteMatrixCut M S T:ℝ) := by
  have hpoint (x : A) (hx : x∈S) : d+T.card-Fintype.card B≤((∑ y∈T,M x y:ℕ):ℝ) := by
    have hc : ∑ y∈Finset.univ\T,M x y≤Fintype.card B-T.card := by
      calc
        _ ≤ ∑ _y∈Finset.univ\T,1 := Finset.sum_le_sum (fun y _=>hM x y)
        _ = _ := by simp [Finset.card_sdiff_of_subset (Finset.subset_univ T)]
    have hs := Finset.sum_sdiff (f:=fun y=>M x y) (Finset.subset_univ T)
    have ht := Finset.card_le_univ T
    have hcr : ((∑ y∈Finset.univ\T,M x y:ℕ):ℝ)≤(Fintype.card B:ℝ)-T.card := by exact_mod_cast hc
    have hsr : ((∑ y∈Finset.univ\T,M x y:ℕ):ℝ)+((∑ y∈T,M x y:ℕ):ℝ)=((∑ y,M x y:ℕ):ℝ) := by exact_mod_cast hs
    linarith only [hcr,hsr,hrow x hx]
  simpa only [bipartiteMatrixCut,Nat.cast_sum,Finset.sum_const,nsmul_eq_mul] using Finset.sum_le_sum hpoint

theorem bipartite_large_cut_numeric
    (a b s t E p δ ε : ℝ) (ha : 0<a) (hb : 0<b) (hs : 0≤s) (ht : 0≤t)
    (hp : 0<p) (hp1 : p≤1) (hδ : δ≤p/16) (hε : ε≤p^2/128)
    (hlarge : (1-2*δ)*a*b<b*s+a*t)
    (hrow : s*(p*b/2+t-b)≤E) (hcol : t*(p*a/2+s-a)≤E)
    (hquad : p*s*t-ε*a*b≤E) :
    p/8*min (b*s) (a*t)≤E := by
  have hcase (a b s t : ℝ) (ha : 0<a) (hb : 0<b) (hs : 0≤s)
      (hlarge : (1-2*δ)*a*b<b*s+a*t) (hle : b*s≤a*t)
      (hrow : s*(p*b/2+t-b)≤E) (hquad : p*s*t-ε*a*b≤E) : p/8*(b*s)≤E := by
    have hab : 0<a*b := mul_pos ha hb
    have hδab := mul_le_mul_of_nonneg_right hδ hab.le
    have hεab := mul_le_mul_of_nonneg_right hε hab.le
    by_cases hsmall : s≤p*a/8
    · have hsb := mul_le_mul_of_nonneg_right hsmall hb.le
      have htlarge : p*b/4≤p*b/2+t-b := by
        apply (mul_le_mul_iff_right₀ ha).mp
        nlinarith only [hlarge,hδab,hsb]
      have hh := mul_le_mul_of_nonneg_left htlarge hs
      have hpos : 0≤p*b*s := mul_nonneg (mul_nonneg hp.le hb.le) hs
      nlinarith only [hh,hrow,hpos]
    · have hslarge : p*a/8≤s := (lt_of_not_ge hsmall).le
      have htlarge : b/4≤t := by
        apply (mul_le_mul_iff_right₀ ha).mp
        have hpab := mul_le_mul_of_nonneg_right hp1 hab.le
        nlinarith only [hlarge,hle,hδab,hpab,hab]
      have hmean := mul_le_mul_of_nonneg_left htlarge (mul_nonneg hp.le hs)
      have herror := mul_le_mul_of_nonneg_right hslarge (mul_nonneg hp.le hb.le)
      have hpos : 0≤p*b*s := mul_nonneg (mul_nonneg hp.le hb.le) hs
      nlinarith only [hmean,herror,hεab,hquad,hpos]
  rcases le_total (b*s) (a*t) with hle|hle
  · rw [min_eq_left hle]
    exact hcase a b s t ha hb hs hlarge hle hrow hquad
  · rw [min_eq_right hle]
    exact hcase b a t s hb ha ht (by nlinarith only [hlarge]) hle hcol (by nlinarith only [hquad])

theorem bipartiteMatrixCut_large_of_degree_and_quadratic
    {A B : Type*} [Fintype A] [Fintype B]
    (M : A → B → ℕ) (hM : ∀ x y,M x y≤1)
    (ha : 0<Fintype.card A) (hb : 0<Fintype.card B)
    (p ρ δ ε : ℝ) (hp : 0<p) (hp1 : p≤1) (hρ : p≤ρ)
    (hδ : δ≤p/16) (hε : ε≤p^2/128)
    (hrow : ∀ x,p*(Fintype.card B:ℝ)/2≤((∑ y,M x y:ℕ):ℝ))
    (hcol : ∀ y,p*(Fintype.card A:ℝ)/2≤((∑ x,M x y:ℕ):ℝ))
    (hcut : ∀ S T,|(bipartiteMatrixCut M S T:ℝ)-ρ*S.card*T.card|≤ε*Fintype.card A*Fintype.card B)
    (S : Finset A) (T : Finset B)
    (hlarge : (1-2*δ)*(Fintype.card A:ℝ)*Fintype.card B<
      (Fintype.card B:ℝ)*S.card+(Fintype.card A:ℝ)*T.card) :
    p/8*min ((Fintype.card B:ℝ)*S.card) ((Fintype.card A:ℝ)*T.card)≤(bipartiteMatrixCut M S T:ℝ) := by
  have hR := bipartiteMatrixCut_row_lower M hM S T (p*(Fintype.card B:ℝ)/2) (fun x _=>hrow x)
  have hC := bipartiteMatrixCut_row_lower (fun y x=>M x y) (fun y x=>hM x y) T S
    (p*(Fintype.card A:ℝ)/2) (fun y _=>hcol y)
  rw [← bipartiteMatrixCut_transpose] at hC
  have hQ : p*S.card*T.card-ε*Fintype.card A*Fintype.card B≤(bipartiteMatrixCut M S T:ℝ) := by
    have hh := (abs_le.mp (hcut S T)).1
    have hmul := mul_le_mul_of_nonneg_right hρ (by positivity : (0:ℝ)≤(S.card:ℝ)*T.card)
    nlinarith only [hh,hmul]
  exact bipartite_large_cut_numeric (Fintype.card A) (Fintype.card B) S.card T.card
    (bipartiteMatrixCut M S T) p δ ε (by exact_mod_cast ha) (by exact_mod_cast hb)
    (by positivity) (by positivity) hp hp1 hδ hε hlarge hR hC hQ

end Oberwolfach
