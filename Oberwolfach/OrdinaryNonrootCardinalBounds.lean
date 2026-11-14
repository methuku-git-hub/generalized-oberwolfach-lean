module

public import Oberwolfach.OrdinaryRestrictedNearBalance

@[expose] public section
/-! Cardinal margins for the nonroot vertex and hub domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_nonroot_cardinal_equalities (T:Finset V) (W:Finset U):
    Fintype.card ↥(Finset.univ\T)+T.card=Fintype.card V ∧
    Fintype.card ↥(Finset.univ\W)+W.card=Fintype.card U:=by
  constructor
  · simpa using (Nat.sub_add_cancel (Finset.card_le_univ T))
  · simpa using (Nat.sub_add_cancel (Finset.card_le_univ W))

theorem ordinary_nonroot_hub_upper (T:Finset V) (W:Finset U)
    (hmargin:T.card+Fintype.card U≤Fintype.card V):
    Fintype.card ↥(Finset.univ\W)≤Fintype.card ↥(Finset.univ\T):=by
  have hc:=ordinary_nonroot_cardinal_equalities T W
  omega

theorem ordinary_nonroot_hub_lower (T:Finset V) (W:Finset U) (ω ωfree:ℝ)
    (hparent:ω*Fintype.card V≤Fintype.card U)
    (hmargin:ωfree*Fintype.card ↥(Finset.univ\T)+(W.card:ℝ)≤ω*Fintype.card V):
    ωfree*Fintype.card ↥(Finset.univ\T)≤Fintype.card ↥(Finset.univ\W):=by
  have hc:=ordinary_nonroot_cardinal_equalities T W
  have hh:((Fintype.card ↥(Finset.univ\W):ℕ):ℝ)+W.card=Fintype.card U:=by exact_mod_cast hc.2
  linarith
theorem ordinary_regular_host_hubs_at_most_half (P:SimpleGraph V) (D:ℕ) (ρ:ℝ)
    (hn:0<Fintype.card V) (hreg:P.IsRegularOfDegree D) (hρ:ρ≤1)
    (hsize:ρ*D=2*(Fintype.card U:ℝ)):
    2*Fintype.card U≤Fintype.card V:=by
  obtain ⟨v⟩:=Fintype.card_pos_iff.mp hn
  have hD:(D:ℝ)≤Fintype.card V:=by
    have hh:=P.degree_lt_card_verts v
    rw [hreg v] at hh
    exact_mod_cast hh.le
  have hρD:ρ*D≤D:=by
    have hh:=mul_nonneg (sub_nonneg.mpr hρ) (show (0:ℝ)≤D by positivity)
    nlinarith
  have hU:(2:ℝ)*Fintype.card U≤Fintype.card V:=by linarith
  exact_mod_cast hU

theorem ordinary_nonroot_hub_upper_from_regular_host (P:SimpleGraph V) (D:ℕ) (ρ:ℝ)
    (T:Finset V) (W:Finset U) (hn:0<Fintype.card V) (hreg:P.IsRegularOfDegree D)
    (hρ:ρ≤1) (hsize:ρ*D=2*(Fintype.card U:ℝ)) (hT:2*T.card≤Fintype.card V):
    Fintype.card ↥(Finset.univ\W)≤Fintype.card ↥(Finset.univ\T):=by
  have hU:=ordinary_regular_host_hubs_at_most_half (U:=U) P D ρ hn hreg hρ hsize
  apply ordinary_nonroot_hub_upper T W
  omega
end Oberwolfach
