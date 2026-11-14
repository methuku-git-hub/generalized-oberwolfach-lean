module

public import Oberwolfach.OrdinaryNonrootCountMargins

@[expose] public section
/-! A single relative bound on the removed roots preserves half the
isolator and transfer count coefficient. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_nonroot_configuration_margins (r k:ℕ) (hr:3≤r) (hk:4≤k)
    (β:ℝ) (hβ:0≤β) (T:Finset V) (W:Finset U)
    (hsmall:((T.card:ℝ)+W.card)*(r:ℝ)^2≤(β/2)*Fintype.card V):
    (β/2)*(Fintype.card ↥(Finset.univ\T):ℝ)^(k-1)+
      ((T.card:ℝ)+W.card)*(Fintype.card V:ℝ)^(k-2)≤β*(Fintype.card V:ℝ)^(k-1) ∧
    (β/2)*(Fintype.card ↥(Finset.univ\T):ℝ)^(r^2)+
      (T.card:ℝ)*(r:ℝ)^2*(Fintype.card V:ℝ)^(r^2-1)≤β*(Fintype.card V:ℝ)^(r^2):=by
  let n:ℝ:=Fintype.card V
  let m:ℝ:=Fintype.card ↥(Finset.univ\T)
  have hn:0≤n:=by dsimp [n];positivity
  have hm:0≤m:=by dsimp [m];positivity
  have hmn:m≤n:=by
    dsimp [m,n]
    exact_mod_cast Fintype.card_le_of_injective (Subtype.val:↥(Finset.univ\T)→V) Subtype.val_injective
  have hr1:(1:ℝ)≤(r:ℝ)^2:=by
    have hh:(1:ℝ)≤r:=by exact_mod_cast (show 1≤r by omega)
    nlinarith
  have hT:(0:ℝ)≤T.card:=by positivity
  have hW:(0:ℝ)≤W.card:=by positivity
  have hsmall':((T.card:ℝ)+W.card)≤(β-β/2)*n:=by
    have hh:=mul_nonneg (sub_nonneg.mpr hr1) (add_nonneg hT hW)
    dsimp [n] at *
    nlinarith only [hsmall,hh]
  have hsmall'':(r:ℝ)^2*(T.card:ℝ)≤(β-β/2)*n:=by
    have hh:=mul_nonneg (sq_nonneg (r:ℝ)) hW
    dsimp [n] at *
    nlinarith only [hsmall,hh]
  have hi:=ordinary_nonroot_count_margin n m ((T.card:ℝ)+W.card) 1 β (β/2) (k-1)
    hn hm hmn (by linarith) (by omega) (by simpa using hsmall')
  have ht:=ordinary_nonroot_count_margin n m (T.card:ℝ) ((r:ℝ)^2) β (β/2) (r^2)
    hn hm hmn (by linarith) (by nlinarith) hsmall''
  constructor
  · have he:k-1-1=k-2:=by omega
    simpa only [one_mul,he,n,m] using hi
  · simpa only [n,m,mul_comm] using ht
end Oberwolfach
