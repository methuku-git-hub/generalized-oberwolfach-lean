module

public import Oberwolfach.ColourResidueRepair
public import Oberwolfach.ParityRepairFromPaths

@[expose] public section

/-! The complete finite repair of a dense edge colouring. The candidate
lower bound is decreased by the realised preliminary recolouring loss;
all parity paths are then chosen simultaneously in that same colouring. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem divisible_colour_repair {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {q h : ℕ} (hq : Even q) (hh : 0<h) (hhq : h∣q)
    (G : SimpleGraph V) (σ : Sym2 V → Fin (q+1)) (ρ : ℝ) (L : ℕ) (hL : 0<L)
    (hreserve : q*h≤(edgeColourGraph G σ (Fin.last q)).edgeFinset.card)
    (hpath : ∀ a : Fin q,∀ u v,u≠v → ρ*Fintype.card V≤
      (colouredTwoPathCount G σ u v a.castSucc (Fin.last q):ℝ))
    (hloss : (q:ℝ)*h≤ρ*Fintype.card V/2)
    (hpack : (q:ℝ)*Fintype.card V/L+4*q+4*L<(ρ/2)*Fintype.card V) :
    ∃ τ : Sym2 V → Fin (q+1),
      (∀ a,(∀ v,Even ((G\edgeColourGraph G τ a).degree v)) ∧
        h∣(G\edgeColourGraph G τ a).edgeFinset.card) ∧
      (∀ a v,|((edgeColourGraph G τ a).degree v:ℝ)-((edgeColourGraph G σ a).degree v:ℝ)|≤q*h+q+1) := by
  obtain ⟨σ',hres,hdeg,hcand⟩ := colour_residue_repair hh hhq G σ hreserve
  have hpath' (a : Fin q) (u v : V) (huv : u≠v) :
      (ρ/2)*Fintype.card V≤(colouredTwoPathCount G σ' u v a.castSucc (Fin.last q):ℝ) := by
    have hh := (abs_le.mp (hcand a.castSucc u v huv)).1
    have hp := hpath a u v huv
    linarith only [hh,hp,hloss]
  obtain ⟨τ,hcard,hpar,hchg⟩ := parity_repair_from_coloured_paths hq G σ' (ρ/2) L hL hpath' hpack
  refine ⟨τ,?_,?_⟩
  · intro a
    refine ⟨hpar a,?_⟩
    apply complement_edge_divisible_of_residue G (edgeColourGraph G τ a) (edgeColourGraph_le G τ a) h
    rw [hcard]
    exact hres a
  · intro a v
    have hh := (abs_sub_le ((edgeColourGraph G τ a).degree v:ℝ)
      ((edgeColourGraph G σ' a).degree v:ℝ) ((edgeColourGraph G σ a).degree v:ℝ)).trans
      (add_le_add (hchg a v) (hdeg a v))
    linarith only [hh]

end Oberwolfach
