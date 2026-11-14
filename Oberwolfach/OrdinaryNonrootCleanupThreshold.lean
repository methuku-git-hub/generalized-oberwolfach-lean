module

public import Oberwolfach.OrdinaryRootFirstPackingWeaken

@[expose] public section
/-! The ambient cleanup threshold dominates the packing threshold on the
injected nonroot domains. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_nonroot_cleanup_threshold (T:Finset V) (W:Finset U) (γ:ℝ) (hγ:0≤γ):
    γ*Fintype.card (↥(Finset.univ\T)⊕↥(Finset.univ\W))≤γ*Fintype.card (V⊕U):=by
  let φ:↥(Finset.univ\T)↪V:=⟨Subtype.val,Subtype.val_injective⟩
  let ψ:↥(Finset.univ\W)↪U:=⟨Subtype.val,Subtype.val_injective⟩
  have hc:Fintype.card (↥(Finset.univ\T)⊕↥(Finset.univ\W))≤Fintype.card (V⊕U):=
    Fintype.card_le_of_injective (φ.sumMap ψ) (φ.sumMap ψ).injective
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hc) hγ
end Oberwolfach
