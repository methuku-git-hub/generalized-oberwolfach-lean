module

public import Oberwolfach.OrdinaryProfileFailureMargins
public import Oberwolfach.OrdinaryProfileCardinalityBounds

@[expose] public section
/-! The degree and four-root row failure terms vanish uniformly. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
theorem ordinary_triangle_failure_margins (A B t ρ:ℝ)
    (hA:0<A) (hB:0<B) (ht:0<t) (hρ:0<ρ):
    ∃ N:ℕ,∀ n:ℕ,N≤n→∀ M₁ M₂:ℝ,
      0≤M₁→M₁≤2*(n:ℝ)^4→0≤M₂→M₂≤256*(n:ℝ)^8→
      M₁*(2*Real.exp (-2*t^2/(A/n)))+
      M₂*(2*Real.exp (-2*(ρ*n)^2/(B*n)))≤2/(n:ℝ)^2 := by
  obtain ⟨N₁,h₁⟩:=constant_deviation_failure_eventually_small 2 A t hA ht 4 2
  obtain ⟨N₂,h₂⟩:=linear_deviation_failure_eventually_small 256 B ρ hB hρ 8 2
  refine ⟨max 1 (max N₁ N₂),?_⟩
  intro n hn M₁ M₂ hM₁ hM₁b hM₂ hM₂b
  have hn0:(0:ℝ)<n:=by exact_mod_cast (show 0<n by omega)
  have hfirst:=h₁ n (by omega) M₁ hM₁ hM₁b
  have hsecond:=h₂ n (by omega) M₂ (B*n) hM₂ hM₂b (mul_pos hB hn0) le_rfl
  calc
    _ ≤ 1/(n:ℝ)^2+1/(n:ℝ)^2 := add_le_add hfirst hsecond
    _ = 2/(n:ℝ)^2 := by ring

theorem ordinary_triangle_profile_cardinality_bounds {V U:Type} [Fintype V] [Fintype U]
    (hn:1≤Fintype.card V) (hu:Fintype.card U≤Fintype.card V):
    (Fintype.card (U×U):ℝ)*(Fintype.card (Sym2 V⊕(V×Unit)):ℝ)≤2*(Fintype.card V:ℝ)^4 ∧
    (Fintype.card V+1:ℝ)^4*(Fintype.card U+1:ℝ)^4≤256*(Fintype.card V:ℝ)^8 := by
  have hc:=ordinary_profile_cardinality_bounds (V:=V) (U:=U) hn hu
  have hnR:(1:ℝ)≤Fintype.card V:=by exact_mod_cast hn
  have huR:(Fintype.card U:ℝ)≤Fintype.card V:=by exact_mod_cast hu
  have hnplus:(Fintype.card V+1:ℝ)≤2*Fintype.card V:=by linarith
  have huplus:(Fintype.card U+1:ℝ)≤2*Fintype.card V:=by linarith
  refine ⟨hc.1,?_⟩
  calc
    _ ≤ (2*(Fintype.card V:ℝ))^4*(2*(Fintype.card V:ℝ))^4 := by gcongr
    _ = _ := by ring
end Oberwolfach
