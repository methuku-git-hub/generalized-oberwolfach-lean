module

public import Oberwolfach.RawIntervalUnassignedGeometry
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

theorem raw_interval_two_unassigned_probability_lower
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (q:Γ→ℝ) (hq:∀g,0≤q g) (hQ:∑g,q g≤1/8)
    (s:Color→ℝ) (hs:∀j,0≤s j) (hS:∑j,s j≤ intervalUncoveredProbability d (∑g,q g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x) (x y:V) (hxy:x≠y):
    (5/8:ℝ)*(1-(∑j,s j)/(intervalUncoveredProbability d (∑g,q g)))^2≤
      (FiniteLaw.pi (rawIntervalCoordinateLaw (V:=V) d hd q hq hQ s hs hS)).probability
      (fun σ=>rawIntervalState π d σ x=none ∧ rawIntervalState π d σ y=none) :=by
  let μ:=rawIntervalCoordinateLaw (V:=V) d hd q hq hQ s hs hS
  let u:=intervalUncoveredProbability d (∑g,q g)
  let lx:RawIntervalCoordinate V:=Sum.inr (Sum.inr x)
  let ly:RawIntervalCoordinate V:=Sum.inr (Sum.inr y)
  let AC:Finset (RawIntervalCoordinate V):=
    Finset.univ.image Sum.inl ∪ Finset.univ.image (fun a:V=>Sum.inr (Sum.inl a))
  let LC:Finset (RawIntervalCoordinate V):={lx,ly}
  let E:=fun σ:RawIntervalOutcome V Γ Color=>¬rawIntervalBlocked π d σ x ∧ ¬rawIntervalBlocked π d σ y
  let B:=fun σ:RawIntervalOutcome V Γ Color=>σ lx=none ∧ σ ly=none
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
    (fun σ=>σ lx=none) (fun σ=>σ ly=none)
    (by intro σ τ h;rw [h lx (by simp)])
    (by intro σ τ h;rw [h ly (by simp)])
  have hB:(FiniteLaw.pi μ).probability B=(1-(∑j,s j)/u)^2:=by
    dsimp only [B]
    rw [hlabel,finiteLaw_pi_coordinate_probability μ lx none,finiteLaw_pi_coordinate_probability μ ly none]
    dsimp [μ,lx,ly,rawIntervalCoordinateLaw,rawIntervalLabelLaw,FiniteLaw.withRemainder,u]
    rw [←Finset.sum_div]
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
  have hr0:0≤1-(∑j,s j)/u:=by
    have hh:(∑j,s j)/u≤1:=(div_le_one hu).2 hS
    linarith
  have hmul:((5:ℝ)/8)*(1-(∑j,s j)/u)^2≤
      (FiniteLaw.pi μ).probability E*(FiniteLaw.pi μ).probability B:=by
    rw [hB]
    exact mul_le_mul_of_nonneg_right (by linarith [hE,hu0]) (sq_nonneg _)
  have hsub:(FiniteLaw.pi μ).probability (fun σ=>E σ ∧ B σ)≤
      (FiniteLaw.pi μ).probability (fun σ=>rawIntervalState π d σ x=none ∧ rawIntervalState π d σ y=none):=by
    apply finiteLaw_probability_mono
    intro σ h
    rcases h with ⟨⟨hx,hy⟩,hlabel⟩
    have hn (v:V) (hblock:¬rawIntervalBlocked π d σ v) (hlabel':σ (Sum.inr (Sum.inr v))=none):
        rawIntervalState π d σ v=none:=by
      apply (rawIntervalState_none_iff π d σ v).2
      exact ⟨by intro g hg;exact hblock (rawIntervalCovered_blocked π d σ v g hg),Or.inr hlabel'⟩
    exact ⟨hn x hx hlabel.1,hn y hy hlabel.2⟩
  rw [hind] at hsub
  exact hmul.trans hsub
theorem raw_interval_two_unassigned_probability_from_slack
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (q:Γ→ℝ) (hq:∀g,0≤q g) (hQ:∑g,q g≤1/8)
    (s:Color→ℝ) (hs:∀j,0≤s j) (hS:∑j,s j≤ intervalUncoveredProbability d (∑g,q g))
    (θ:ℝ) (hθ:0<θ) (hrem:θ≤1-(∑g,q g)-(∑j,s j))
    (hspace:1/(8*(d:ℝ))≤θ/2)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x) (x y:V) (hxy:x≠y):
    (5/32:ℝ)*θ^2≤(FiniteLaw.pi (rawIntervalCoordinateLaw (V:=V) d hd q hq hQ s hs hS)).probability
      (fun σ=>rawIntervalState π d σ x=none ∧ rawIntervalState π d σ y=none):=by
  let Q:=∑g,q g
  let S:=∑j,s j
  let u:=intervalUncoveredProbability d Q
  have hQ0:0≤Q:=Finset.sum_nonneg (fun g _=>hq g)
  have hS0:0≤S:=Finset.sum_nonneg (fun j _=>hs j)
  have hu0:(13:ℝ)/16≤u:=intervalUncoveredProbability_lower d hd Q hQ0 hQ
  have hu:0<u:=by linarith
  have hd0:(0:ℝ)<d:=by exact_mod_cast (show 0<d by omega)
  have hu1:u≤1:=by
    dsimp [u,intervalUncoveredProbability]
    have hh:0≤(1+1/(d:ℝ))*Q:=mul_nonneg (by positivity) hQ0
    linarith
  have hQd:Q/(d:ℝ)≤1/(8*(d:ℝ)):=by
    have hh:=div_le_div_of_nonneg_right hQ hd0.le
    calc
      _ ≤ (1/8:ℝ)/(d:ℝ):=hh
      _ = _:=by ring
  have hrem':θ≤1-Q-S:=hrem
  have huS:θ/2≤u-S:=by
    dsimp [u,intervalUncoveredProbability]
    have heq:(1+1/(d:ℝ))*Q=Q+Q/(d:ℝ):=by ring
    rw [heq]
    linarith
  have hr:θ/2≤1-S/u:=by
    have hθu:(θ/2)*u≤θ/2:=by nlinarith
    have heq:1-S/u=(u-S)/u:=by field_simp
    rw [heq]
    exact (le_div_iff₀ hu).2 (by nlinarith)
  have hsq:(θ/2)^2≤(1-S/u)^2:=by nlinarith
  have hh:=raw_interval_two_unassigned_probability_lower π d hd q hq hQ s hs hS hnoshort x y hxy
  have hc:=mul_le_mul_of_nonneg_left hsq (show (0:ℝ)≤5/8 by norm_num)
  dsimp only [S,Q,u] at hc
  nlinarith [hh,hc]
end Oberwolfach
