module

public import Oberwolfach.CyclicInterfaceData
public import Oberwolfach.FractionalCycleAssembly

@[expose] public section

/-! The degree marginals, residual maps and sector weights of the actual
cyclic interface construction. These formulas are shared by its existence
proof and the pointwise estimates for the same weights. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {X Y : Type*} [Fintype X] [Fintype Y]

def cyclicInterfaceMarginal (L : Fin (k + 2) → X → Y → Prop)
    (i : Fin (k + 2)) (x : X) : ℝ :=
  cyclicInterfaceDegree L i x / (k + 2 : ℝ)

def cyclicResidualSystem (L : Fin (k + 2) → X → Y → Prop)
    (R : Fin (k + 2) → Y → X → Prop)
    (Q : transportProduct (cyclicInterfaceMarginal L) (finRotate (k + 2)))
    (i : Fin (k + 2)) : X → X → ℝ :=
  intervalResidualMap (L i) (R i) (k + 2 : ℝ) (Q.val i)

def cyclicReservePath (L : Fin (k + 2) → X → Y → Prop)
    (R : Fin (k + 2) → Y → X → Prop)
    (Q : transportProduct (cyclicInterfaceMarginal L) (finRotate (k + 2)))
    (i : Fin (k + 2)) (p : X × Y × X) : ℝ :=
  endpointReserve (L i) (R i) (Q.val i) p.1 p.2.1 p.2.2

def cyclicResidualPath (L : Fin (k + 2) → X → Y → Prop)
    (R : Fin (k + 2) → Y → X → Prop)
    (Q : transportProduct (cyclicInterfaceMarginal L) (finRotate (k + 2)))
    (i : Fin (k + 2)) (p : X × Y × X) : ℝ :=
  scaledResidualPath (interfaceCapacity (L i)) (interfaceCapacity (R i))
    (endpointReserve (L i) (R i) (Q.val i)) (k + 2 : ℝ) p.1 p.2.1 p.2.2

def cyclicSectorWeight (L : Fin (k + 2) → X → Y → Prop)
    (R : Fin (k + 2) → Y → X → Prop)
    (Q : transportProduct (cyclicInterfaceMarginal L) (finRotate (k + 2)))
    (c : Fin (k + 2)) (p : Fin (k + 2) → X × Y × X) : ℝ :=
  chainJoint (cyclicInterfaceMarginal L) (cyclicResidualSystem L R Q)
    (finRotate (k + 2)) (finRotate (k + 2) c) (k + 1)
    (fun j => (p (cyclicChainOrder c j)).1) *
    ∏ i, (if i = c then cyclicReservePath L R Q i (p i)
      else cyclicResidualPath L R Q i (p i)) /
      (if i = c then Q.val c (p i).1 (p i).2.2
        else cyclicResidualSystem L R Q i (p i).1 (p i).2.2)

end Oberwolfach
