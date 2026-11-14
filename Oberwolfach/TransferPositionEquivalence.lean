module

public import Oberwolfach.TransferGreedyOrder

@[expose] public section

/-! The ordered free positions are exactly the r squared distinct labels
of the transfer; no labels are identified or lost by the ordering. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def transferFreePosition (r : ℕ) (hr : 3 ≤ r) : (Fin r×Fin r) ↪ Fin (r^2) where
  toFun a := ⟨transferVertexPosition r a.1 a.2-1,by
    have hh := transferVertexPosition_bounds r hr a.1 a.2
    omega⟩
  inj' := by
    intro a b he
    have hh := congrArg Fin.val he
    have ha := transferVertexPosition_bounds r hr a.1 a.2
    have hb := transferVertexPosition_bounds r hr b.1 b.2
    apply transferVertexPosition_injective r hr
    change transferVertexPosition r a.1 a.2=transferVertexPosition r b.1 b.2
    change transferVertexPosition r a.1 a.2-1=transferVertexPosition r b.1 b.2-1 at hh
    omega

def transferPositionEquiv (r : ℕ) (hr : 3 ≤ r) : (Fin r×Fin r) ≃ Fin (r^2) :=
  Equiv.ofBijective (transferFreePosition r hr)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨(transferFreePosition r hr).injective,by
      simp only [Fintype.card_prod,Fintype.card_fin,pow_two]⟩)

def transferFullPosition (r : ℕ) (hr : 3 ≤ r) (a : Fin r×Fin r) : Fin (r^2+1) :=
  (transferFreePosition r hr a).succ

theorem transferFullPosition_val (r : ℕ) (hr : 3 ≤ r) (a : Fin r×Fin r) :
    (transferFullPosition r hr a:ℕ)=transferVertexPosition r a.1 a.2 := by
  have hp := (transferVertexPosition_bounds r hr a.1 a.2).1
  change transferVertexPosition r a.1 a.2-1+1=transferVertexPosition r a.1 a.2
  omega

theorem transferFullPosition_injective (r : ℕ) (hr : 3 ≤ r) :
    Function.Injective (transferFullPosition r hr) := by
  intro a b h
  apply (transferFreePosition r hr).injective
  exact Fin.succ_inj.mp h

end Oberwolfach
