module

public import Oberwolfach.OrdinaryRootCoverNonrootData

@[expose] public section
/-! Normalize the actual fine-cover bounds by the physical parent size;
this preserves the exact selected cover and keeps its deep cost proportional
to the next parent rather than replacing it by a larger uniform rate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_fine_cover_normalized_rates_general_load
    (m loadK:ℕ) (I T:Finset V) (W:Finset U) (ξ κ lam:ℝ)
    (hn:0<Fintype.card V) (hξ:0≤ξ) (hκ:0≤κ) (hlam:0≤lam)
    (hroots:(T.card:ℝ)+W.card≤lam*Fintype.card V):
    let n:ℝ:=Fintype.card V;let N:ℝ:=Fintype.card (V⊕U);
    let cover:=10*ξ*I.card;
    let ell:=max (18*κ*n+3*((W.card:ℝ)+((loadK:ℝ)+1)*T.card)) (3*κ*n*((m:ℝ)+1)+(T.card:ℝ)*((m:ℝ)+1));
    let ηrate:=cover/N;let ellrate:=ell/N;
    0<N ∧ 0≤ηrate ∧ 0≤ellrate ∧ ηrate*N=cover ∧ ellrate*N=ell ∧
    ηrate≤10*ξ ∧ ellrate≤max (18*κ+3*((loadK+1)*lam)) ((3*κ+lam)*((m:ℝ)+1)):=by
  intro n N cover ell ηrate ellrate
  have hnR:0<n:=by dsimp [n];exact_mod_cast hn
  have hnN:n≤N:=by dsimp [n,N];exact_mod_cast (Fintype.card_le_of_injective (Sum.inl:V→V⊕U) Sum.inl_injective)
  have hN:0<N:=hnR.trans_le hnN
  have hI:(I.card:ℝ)≤n:=by dsimp [n];exact_mod_cast Finset.card_le_univ I
  have hT:0≤(T.card:ℝ):=by positivity
  have hW:0≤(W.card:ℝ):=by positivity
  have hcover:0≤cover:=by dsimp [cover];positivity
  have hell:0≤ell:=by dsimp [ell];positivity
  have hη:0≤ηrate:=by dsimp [ηrate];positivity
  have he:0≤ellrate:=by dsimp [ellrate];positivity
  have hηeq:ηrate*N=cover:=by dsimp [ηrate];exact div_mul_cancel₀ _ (ne_of_gt hN)
  have heeq:ellrate*N=ell:=by dsimp [ellrate];exact div_mul_cancel₀ _ (ne_of_gt hN)
  have hηcap:ηrate≤10*ξ:=by
    apply (div_le_iff₀ hN).mpr
    dsimp [ηrate,cover]
    nlinarith [mul_le_mul_of_nonneg_left hI (show 0≤10*ξ by positivity),
      mul_le_mul_of_nonneg_left hnN (show 0≤10*ξ by positivity)]
  let E:ℝ:=max (18*κ+3*((loadK+1)*lam)) ((3*κ+lam)*((m:ℝ)+1))
  have hE:0≤E:=by dsimp [E];positivity
  have hm0:0≤((m:ℝ)+1):=by positivity
  have he1:18*κ*n+3*((W.card:ℝ)+((loadK:ℝ)+1)*T.card)≤E*n:=by
    have hK0:(0:ℝ)≤loadK:=by positivity
    have hmult:=mul_le_mul_of_nonneg_left hroots (show (0:ℝ)≤(loadK:ℝ)+1 by positivity)
    have hmax:=mul_le_mul_of_nonneg_right (le_max_left (18*κ+3*((loadK+1)*lam)) ((3*κ+lam)*((m:ℝ)+1))) hnR.le
    dsimp [E] at *
    nlinarith [mul_nonneg hK0 hW]
  have he2:3*κ*n*((m:ℝ)+1)+(T.card:ℝ)*((m:ℝ)+1)≤E*n:=by
    have ht:(T.card:ℝ)≤lam*n:=by linarith only [hroots,hW]
    have ht':=mul_le_mul_of_nonneg_right ht hm0
    have hmax:=mul_le_mul_of_nonneg_right (le_max_right (18*κ+3*((loadK+1)*lam)) ((3*κ+lam)*((m:ℝ)+1))) hnR.le
    dsimp [E] at *
    nlinarith only [ht',hmax]
  have hellBound:ell≤E*N:=by
    have hh:ell≤E*n:=by dsimp [ell];exact max_le he1 he2
    exact hh.trans (mul_le_mul_of_nonneg_left hnN hE)
  have hecap:ellrate≤E:=by
    dsimp [ellrate]
    exact (div_le_iff₀ hN).mpr hellBound
  exact ⟨hN,hη,he,hηeq,heeq,hηcap,hecap⟩
end Oberwolfach
