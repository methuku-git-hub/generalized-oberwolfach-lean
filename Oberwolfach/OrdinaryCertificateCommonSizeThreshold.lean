module

public import Oberwolfach.OrdinaryVortexGeneralCertificateInnerBounds

@[expose] public section
/-! A single late size threshold absorbs the certificate's fixed conflict
budget and any previously selected finite thresholds at every vortex level. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_certificate_common_size_threshold
    (Lconf kcap ε:ℝ) (hkcap:0<kcap) (hε:0<ε) (Nbase:ℕ):
    ∃M:ℕ,1≤M ∧ Nbase≤M ∧ 4/ε≤(M:ℝ) ∧ Lconf≤kcap^2*M :=by
  have hk:0<kcap^2:=sq_pos_of_pos hkcap
  obtain ⟨N,hN⟩:=exists_nat_gt (max (4/ε) (Lconf/kcap^2))
  let M:=max (max Nbase 1) N
  have hNM:N≤M:=le_max_right _ _
  have hMN:(N:ℝ)≤M:=by exact_mod_cast hNM
  have hlarge:4/ε<(N:ℝ):=(le_max_left _ _).trans_lt hN
  have hbudget:Lconf<kcap^2*(N:ℝ):=by
    have hh:Lconf/kcap^2<(N:ℝ):=(le_max_right _ _).trans_lt hN
    have hh':= (div_lt_iff₀ hk).mp hh
    nlinarith only [hh']
  refine ⟨M,?_,?_,?_,?_⟩
  · exact (le_max_right Nbase 1).trans (le_max_left _ _)
  · exact (le_max_left Nbase 1).trans (le_max_left _ _)
  · exact hlarge.le.trans hMN
  · exact hbudget.le.trans (mul_le_mul_of_nonneg_left hMN hk.le)

theorem ordinary_certificate_budget_at_inner_size
    {V U:Type} [Fintype V] [Fintype U] (I:Finset V) (M:ℕ) (Lconf kcap:ℝ)
    (hM:M≤I.card) (hbudget:Lconf≤kcap^2*M):
    Lconf≤kcap^2*Fintype.card (V⊕U) :=by
  have hIV:I.card≤Fintype.card V:=Finset.card_le_univ I
  have hVU:Fintype.card V≤Fintype.card (V⊕U):=
    Fintype.card_le_of_injective Sum.inl Sum.inl_injective
  have hMn:(M:ℝ)≤Fintype.card (V⊕U):=by exact_mod_cast hM.trans (hIV.trans hVU)
  exact hbudget.trans (mul_le_mul_of_nonneg_left hMn (sq_nonneg kcap))
end Oberwolfach
