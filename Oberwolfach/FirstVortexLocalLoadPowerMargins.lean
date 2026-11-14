module

public import Oberwolfach.FirstVortexMatchingScalePositive
public import Oberwolfach.PartitionMargins
public import Oberwolfach.VortexSizeBounds

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_local_load_power_margins
    (ε δ θ:ℝ) (hε:0<ε) (hδ:0<δ) (hθ:0<θ):
    ∃N:ℕ,∀n:ℕ,N≤n→∀(U:Type) [Fintype U] (G:SimpleGraph (Fin n))
      (D m:ℕ) (β:ℝ) (Q:Vortex U G D β ε m),0<m→
      let A:ℝ:=(Q.extendedVertices 1).card
      4*A^(3/4:ℝ)≤δ*A/8 ∧ A^(3/4:ℝ)≤(θ/4096)*A :=by
  let c:ℝ:=min (δ/32) (θ/4096)
  have hc:0<c:=by dsimp [c]; positivity
  obtain ⟨T,hT⟩:=eventually_sublinear_le_linear (p:=(3/4:ℝ)) (ε:=c) (by norm_num) hc
  obtain ⟨N,hN⟩:=exists_nat_gt (2*(T:ℝ)/ε)
  refine ⟨N,?_⟩
  intro n hn U _ G D m β Q hm A
  have hnR:(N:ℝ)≤n:=by exact_mod_cast hn
  have hbig:(2*(T:ℝ))<ε*n:=by
    have h:= (div_lt_iff₀ hε).mp hN
    have hmul := mul_le_mul_of_nonneg_right hnR hε.le
    nlinarith only [h, hmul]
  have hsize:ε*(n:ℝ)/2≤((Q.extendedVertices 1).card:ℝ):=by
    simpa only [Fintype.card_fin] using Q.first_inner_vertex_size_lower_of_positive_terminal_size hε hm
  have hTA:T≤(Q.extendedVertices 1).card:=by exact_mod_cast (show (T:ℝ)≤((Q.extendedVertices 1).card:ℝ) by linarith)
  have hpow:=hT (Q.extendedVertices 1).card hTA
  have hA:0≤A:=by dsimp [A]; positivity
  have hcδ:c≤δ/32:=min_le_left _ _
  have hcθ:c≤θ/4096:=min_le_right _ _
  have hδ' := mul_le_mul_of_nonneg_right hcδ hA
  have hθ' := mul_le_mul_of_nonneg_right hcθ hA
  constructor <;> dsimp [A] at * <;> nlinarith

theorem first_vortex_spacing_load_margin
    (θ δ:ℝ) (d:ℕ) (hθ:0≤θ) (hδ:10*θ≤δ) (hd:1/(d:ℝ)≤θ/1024):
    4/(d:ℝ)≤δ/8 :=by
  have hfour:4/(d:ℝ)=4*(1/(d:ℝ)):=by ring
  rw [hfour]
  nlinarith

theorem first_vortex_inner_hub_card_le_vertex_card
    {n D m:ℕ} {U:Type} [Fintype U] {G:SimpleGraph (Fin n)} {β ε:ℝ}
    (Q:Vortex U G D β ε m) (hreg:G.IsRegularOfDegree D) (hn:0<n)
    (hD:0<D) (hε:0≤ε) (hρ:initialIndexDensity U D≤1):
    ((Q.extendedIndices 1).card:ℝ)≤(Q.extendedVertices 1).card :=by
  have h:=Q.extended_index_size_upper hreg (by simpa using hn) hD hε hρ 1
  have hcard:(Q.extendedIndices 1).card≤(Q.extendedVertices 1).card:=by omega
  exact_mod_cast hcard
end Oberwolfach
