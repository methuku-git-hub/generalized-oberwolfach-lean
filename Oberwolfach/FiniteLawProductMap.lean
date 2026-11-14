module

public import Oberwolfach.FiniteProductRegrouping

@[expose] public section
/-! Mapping one coordinate of a product law preserves the other coordinate. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_prod_map_left {Ω Γ Ξ:Type} [Fintype Ω] [Fintype Γ] [Fintype Ξ]
    (μ:FiniteLaw Ω) (ν:FiniteLaw Γ) (f:Ω→Ξ):
    (μ.prod ν).map (fun z=>(f z.1,z.2))=(μ.map f).prod ν:=by
  apply finiteLaw_ext
  intro z
  have hh:=finiteLaw_prod_map_left_probability μ ν f (fun x y=>(x,y)=z)
  have hm:=finiteLaw_map_probability (μ.prod ν) (fun z=>(f z.1,z.2)) (fun w=>w=z)
  have hp:=hm.trans hh
  simpa [FiniteLaw.probability,eq_comm] using hp

theorem finiteLaw_categorical_direction_prod {k:ℕ} (ρ:Fin k→ℝ)
    (hρ:∀ a,0≤ρ a) (htotal:∑ a,ρ a=1):
    FiniteLaw.categoricalDirection ρ hρ htotal=(FiniteLaw.categorical ρ hρ htotal).prod FiniteLaw.fairCoin:=by
  apply finiteLaw_ext
  rintro ⟨a,b⟩
  simp [FiniteLaw.categoricalDirection,FiniteLaw.categorical,FiniteLaw.prod,FiniteLaw.fairCoin]
  ring
end Oberwolfach
