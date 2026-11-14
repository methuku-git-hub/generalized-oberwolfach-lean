module

public import Oberwolfach.RawIntervalDistribution
public import Oberwolfach.GoodPlacementEvents

@[expose] public section
/-! Two distinct ordinary labels have a uniform joint lower probability even
when their permutation windows overlap. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V Γ Color:Type} [Fintype V] [DecidableEq V] [Fintype Γ] [Fintype Color]

theorem raw_interval_two_labels_probability_lower
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (q:Γ→ℝ) (hq:∀g,0≤q g) (hQ:∑g,q g≤1/8)
    (s:Color→ℝ) (hs:∀j,0≤s j) (hS:∑j,s j≤ intervalUncoveredProbability d (∑g,q g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x) (x y:V) (hxy:x≠y) (j:Color):
    (5/8:ℝ)*(s j)^2≤(FiniteLaw.pi (rawIntervalCoordinateLaw (V:=V) d hd q hq hQ s hs hS)).probability
      (fun σ=>rawIntervalState π d σ x=some (Sum.inr j) ∧ rawIntervalState π d σ y=some (Sum.inr j)) :=by
  let μ:=rawIntervalCoordinateLaw (V:=V) d hd q hq hQ s hs hS
  let u:=intervalUncoveredProbability d (∑g,q g)
  let lx:RawIntervalCoordinate V:=Sum.inr (Sum.inr x)
  let ly:RawIntervalCoordinate V:=Sum.inr (Sum.inr y)
  let AC:Finset (RawIntervalCoordinate V):=
    Finset.univ.image Sum.inl ∪ Finset.univ.image (fun a:V=>Sum.inr (Sum.inl a))
  let LC:Finset (RawIntervalCoordinate V):={lx,ly}
  let E:=fun σ:RawIntervalOutcome V Γ Color=>¬rawIntervalBlocked π d σ x ∧ ¬rawIntervalBlocked π d σ y
  let B:=fun σ:RawIntervalOutcome V Γ Color=>σ lx=some j ∧ σ ly=some j
  have hdisj:Disjoint AC LC:=by
    apply Finset.disjoint_left.mpr
    intro e he hf
    simp only [LC,Finset.mem_insert,Finset.mem_singleton] at hf
    rcases hf with rfl|rfl <;> simp [AC,lx,ly] at he
  have hind:=finiteLaw_disjoint_supported_events μ AC LC hdisj E B
    (by
      intro σ τ hagree
      have hA (a:V):σ (Sum.inl a)=τ (Sum.inl a):=by apply hagree;simp [AC]
      have hG (a:V):σ (Sum.inr (Sum.inl a))=τ (Sum.inr (Sum.inl a)):=by apply hagree;simp [AC]
      dsimp only [E,rawIntervalBlocked,rawIntervalColouredStart,rawIntervalKept]
      simp_rw [hA,hG])
    (by
      intro σ τ hagree
      have hx:=hagree lx (by simp [LC])
      have hy:=hagree ly (by simp [LC])
      dsimp only [B]
      rw [hx,hy])
  have hxycoord:lx≠ly:=by simp [lx,ly,hxy]
  have hlabel:=finiteLaw_disjoint_supported_events μ {lx} {ly}
    (by simp [Finset.disjoint_singleton,hxycoord])
    (fun σ=>σ lx=some j) (fun σ=>σ ly=some j)
    (by intro σ τ h;rw [h lx (by simp)])
    (by intro σ τ h;rw [h ly (by simp)])
  have hB:(FiniteLaw.pi μ).probability B=(s j/u)^2:=by
    dsimp only [B]
    rw [hlabel,finiteLaw_pi_coordinate_probability μ lx (some j),finiteLaw_pi_coordinate_probability μ ly (some j)]
    change (s j/u)*(s j/u)=(s j/u)^2
    ring
  have hux: (FiniteLaw.pi μ).probability (fun σ=>¬rawIntervalBlocked π d σ x)=u:=
    rawIntervalUnblocked_probability π d hd q hq hQ s hs hS hnoshort x
  have huy: (FiniteLaw.pi μ).probability (fun σ=>¬rawIntervalBlocked π d σ y)=u:=
    rawIntervalUnblocked_probability π d hd q hq hQ s hs hS hnoshort y
  have hE:2*u-1≤(FiniteLaw.pi μ).probability E:=by
    have hh:=finiteLaw_good_intersection (FiniteLaw.pi μ) (fun σ=>¬rawIntervalBlocked π d σ x)
      (fun σ=>¬rawIntervalBlocked π d σ y) (1-u) (by linarith [huy])
    dsimp only [E]
    linarith [hux]
  have hu0:(13:ℝ)/16≤u:=intervalUncoveredProbability_lower d hd (∑g,q g)
    (Finset.sum_nonneg (fun g _=>hq g)) hQ
  have hu1:u≤1:=by
    dsimp [u,intervalUncoveredProbability]
    have hnonneg:0≤(1+1/(d:ℝ))*(∑g,q g):=mul_nonneg (by positivity) (Finset.sum_nonneg (fun g _=>hq g))
    linarith
  have hu:0<u:=by linarith
  have hsj:0≤s j:=hs j
  have hdiv:s j≤s j/u:=by
    apply (le_div_iff₀ hu).mpr
    nlinarith
  have hsq:(s j)^2≤(s j/u)^2:=by nlinarith
  have hB0:0≤(s j/u)^2:=sq_nonneg _
  have hmul:((5:ℝ)/8)*(s j/u)^2≤(FiniteLaw.pi μ).probability E*(FiniteLaw.pi μ).probability B:=by
    rw [hB]
    exact mul_le_mul_of_nonneg_right (by linarith [hE,hu0]) hB0
  have hstates:(FiniteLaw.pi μ).probability (fun σ=>E σ ∧ B σ)=
      (FiniteLaw.pi μ).probability (fun σ=>rawIntervalState π d σ x=some (Sum.inr j) ∧ rawIntervalState π d σ y=some (Sum.inr j)):=by
    congr 1
    funext σ
    apply propext
    simp only [E,B,lx,ly,rawIntervalState_label_iff]
    tauto
  rw [←hstates,hind]
  exact (mul_le_mul_of_nonneg_left hsq (by norm_num)).trans hmul
end Oberwolfach
