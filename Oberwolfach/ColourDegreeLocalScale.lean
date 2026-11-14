module

public import Oberwolfach.ColourDegrees

@[expose] public section
/-! Colour-degree concentration at the size of the tested neighbourhood. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem sampledColourDegree_tail_at_scale
    {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} (Z : SimpleGraph V)
    (ρ : Fin k → ℝ) (hρ : ∀ a, 0 ≤ ρ a) (htotal : ∑ a, ρ a = 1)
    (a : Fin k) (x : V) (N : ℝ) (hN : (Z.degree x:ℝ) ≤ N) {t : ℝ} (ht : 0 ≤ t) :
    (FiniteLaw.pi (fun _ : Sym2 V => FiniteLaw.categorical ρ hρ htotal)).probability
      (fun c => t ≤ |(sampledColourDegree Z c a x : ℝ) - ρ a * Z.degree x|) ≤
      2 * Real.exp (-2 * t ^ 2 / N) := by
  have hh := finiteLaw_singleton_patterns_tail_at_scale
    (fun _ : Sym2 V => FiniteLaw.categorical ρ hρ htotal)
    (Z.neighborFinset x) (fun y => s(x, y)) (fun _ _ => a)
    (fun _ _ _ _ h => incidentPair_injective x h)
    (n := N) (by simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hN) ht
  have hmass : (FiniteLaw.categorical ρ hρ htotal).mass a = ρ a := rfl
  simp only [hmass, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul,
    ← sampledColourDegree_patterns] at hh
  simpa only [mul_comm (Z.degree x : ℝ)] using hh

theorem sampledColourDegree_joint_tail_at_scale
    {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} (Z : SimpleGraph V)
    (ρ : Fin k → ℝ) (hρ : ∀ a, 0 ≤ ρ a) (htotal : ∑ a, ρ a = 1)
    (a : Fin k) (x : V) (N : ℝ) (hN : (Z.degree x:ℝ) ≤ N) {t : ℝ} (ht : 0 ≤ t) :
    (FiniteLaw.pi (fun _ : Sym2 V => FiniteLaw.categoricalDirection ρ hρ htotal)).probability
      (fun σ => t ≤ |(sampledColourDegree Z (fun e => (σ e).1) a x : ℝ) - ρ a * Z.degree x|) ≤
      2 * Real.exp (-2 * t ^ 2 / N) := by
  have hm := categoricalDirection_colour_probability (E := Sym2 V) ρ hρ htotal
    (fun c => t ≤ |(sampledColourDegree Z c a x : ℝ) - ρ a * Z.degree x|)
  rw [hm]
  exact sampledColourDegree_tail_at_scale Z ρ hρ htotal a x N hN ht
end Oberwolfach
