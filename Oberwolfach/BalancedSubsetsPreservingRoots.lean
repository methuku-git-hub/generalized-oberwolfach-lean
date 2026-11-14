module

public import Oberwolfach.Neighbourhoods

@[expose] public section

/-! Trim two finite classes to an exact integer ratio while retaining
prescribed roots. The loss is controlled by the original cardinal imbalance. -/
set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [DecidableEq V]

 theorem balanced_trim_numerical (a b s:ℕ) (hs:1≤s):
    let k:=min a (b/s)
    k≤a∧s*k≤b∧
      ((a:ℝ)-k+(b:ℝ)-s*k≤|(b:ℝ)-s*a|+s-1):=by
  intro k
  have hs0:0<s:=by omega
  have hq:s*(b/s)≤b:=Nat.mul_div_le b s
  have hr:b%s<s:=Nat.mod_lt b hs0
  have hb:s*(b/s)+b%s=b:=by simpa only [Nat.mul_comm,add_comm] using Nat.mod_add_div b s
  have hka:k≤a:=min_le_left _ _
  have hkb:k≤b/s:=min_le_right _ _
  refine ⟨hka,(Nat.mul_le_mul_left s hkb).trans hq,?_⟩
  have hsR:(1:ℝ)≤s:=by exact_mod_cast hs
  by_cases hab:a≤b/s
  · have hk:k=a:=min_eq_left hab
    rw [hk]
    have hsa:s*a≤b:=(Nat.mul_le_mul_left s hab).trans hq
    have hp':(s:ℝ)*a≤b:=by exact_mod_cast hsa
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hk:k=b/s:=min_eq_right (by omega)
    rw [hk]
    have hqa:b/s+1≤a:=by omega
    have hqaR:((b/s:ℕ):ℝ)+1≤a:=by exact_mod_cast hqa
    have hrR:((b%s:ℕ):ℝ)≤s-1:=by
      have hh:((b%s:ℕ):ℝ)+1≤s:=by exact_mod_cast (show b%s+1≤s by omega)
      linarith
    have hbR:(s:ℝ)*(b/s:ℕ)+(b%s:ℕ)=b:=by exact_mod_cast hb
    have hn:(0:ℝ)≤((s:ℝ)-1)*((a:ℝ)-(b/s:ℕ)-1):=mul_nonneg (by linarith) (by linarith)
    have hneg:(b:ℝ)-s*a≤0:=by nlinarith only [hsR,hqaR,hrR,hbR,hn]
    rw [abs_of_nonpos hneg]
    nlinarith only [hsR,hqaR,hrR,hbR,hn]

 theorem balanced_subsets_preserving_roots (A B ZA ZB:Finset V) (s:ℕ) (hs:1≤s)
    (hZA:ZA⊆A) (hZB:ZB⊆B) (hZ:ZB.card=s*ZA.card):
    ∃ A' B':Finset V,ZA⊆A'∧A'⊆A∧ZB⊆B'∧B'⊆B∧
      B'.card=s*A'.card∧A'.card=min A.card (B.card/s)∧
      ((A.card:ℝ)-A'.card+(B.card:ℝ)-B'.card≤|(B.card:ℝ)-s*A.card|+s-1):=by
  let k:=min A.card (B.card/s)
  have hka:k≤A.card:=min_le_left _ _
  have hkb:s*k≤B.card:=(balanced_trim_numerical A.card B.card s hs).2.1
  have hZk:ZA.card≤k:=by
    apply le_min (Finset.card_le_card hZA)
    apply (Nat.le_div_iff_mul_le (by omega)).mpr
    simpa only [Nat.mul_comm,hZ] using (Finset.card_le_card hZB)
  obtain ⟨A',hZA',hA',hAc⟩:=Finset.exists_subsuperset_card_eq hZA hZk hka
  obtain ⟨B',hZB',hB',hBc⟩:=Finset.exists_subsuperset_card_eq hZB
    (by rw [hZ];exact Nat.mul_le_mul_left s hZk) hkb
  refine ⟨A',B',hZA',hA',hZB',hB',by rw [hAc,hBc],hAc,?_⟩
  rw [hAc,hBc,Nat.cast_mul]
  exact (balanced_trim_numerical A.card B.card s hs).2.2

end Oberwolfach
