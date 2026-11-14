module

public import Oberwolfach.OrdinaryBalancedRootCounts

@[expose] public section

/-! Total rim/spoke equality and cycle-length divisibility follow from
local row balance and hub divisibility, without a decomposition premise. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_balanced_total_edges (G : SimpleGraph V) (H : V → U → Prop)
    (hbal : ∀ v,G.degree v=2*(Finset.univ.filter (H v)).card) :
    G.edgeFinset.card=Fintype.card {e:V×U // H e.1 e.2} := by
  exact (balanced_root_edge_counts G H hbal (Fintype.card V) (Fintype.card U)
    (fun _ => Finset.card_le_univ _) (Fintype.card_subtype_le _)).1

theorem ordinary_spoke_total_divisible (H : V → U → Prop) (r : ℕ)
    (hdiv : ∀ u,r∣(Finset.univ.filter (fun v => H v u)).card) :
    r∣Fintype.card {e:V×U // H e.1 e.2} := by
  let e : {e:V×U // H e.1 e.2} ≃ (Σ u,{v:V // H v u}) := {
    toFun := fun a => ⟨a.val.2,⟨a.val.1,a.property⟩⟩
    invFun := fun a => ⟨(a.2.val,a.1),a.2.property⟩
    left_inv := by rintro ⟨⟨v,u⟩,h⟩;rfl
    right_inv := by rintro ⟨u,⟨v,h⟩⟩;rfl }
  rw [Fintype.card_congr e,Fintype.card_sigma]
  simp only [Fintype.card_subtype]
  exact Finset.dvd_sum (fun u _ => hdiv u)

theorem ordinary_balanced_rim_total_divisible (G : SimpleGraph V) (H : V → U → Prop) (r : ℕ)
    (hbal : ∀ v,G.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv : ∀ u,r∣(Finset.univ.filter (fun v => H v u)).card) : r∣G.edgeFinset.card := by
  rw [ordinary_balanced_total_edges G H hbal]
  exact ordinary_spoke_total_divisible H r hdiv

end Oberwolfach
