module

public import Oberwolfach.OrdinaryUniformProtectedBalanceHistory
public import Oberwolfach.VortexExtended

@[expose] public section
/-! Extract the current local window from a single uniform vortex history. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinary_vortex_uniform_balance_history_at
    (P Q:SimpleGraph V) (H:V→U→Prop) (D m:ℕ) (β ε:ℝ) (Vort:Vortex U P D β ε m)
    (r i L buffer:ℕ) (cost deepCost:ℕ→ℝ) (A:Finset (Sym2 V⊕(V×U))) (inner cross:ℕ→ℕ→ℝ)
    (h:OrdinaryUniformProtectedBalanceHistory Q H
      (fun t=>Vort.extendedVertices (t+1)) (fun t=>Vort.extendedVertices (t+buffer))
      (fun t=>Vort.extendedIndices (t+1)) (fun t=>Vort.extendedIndices (t+buffer))
      cost deepCost r (i+1) L A
      (fun t=>Vort.extendedVertices (t+2)) (fun t=>Vort.extendedVertices (t+1))
      (fun t=>Vort.extendedIndices (t+2)) (fun t=>Finset.Icc (t+3-buffer) t) inner cross)
    (hi:i<L):
    OrdinaryProtectedWindowBalanceHistory Q H
      (fun t=>Vort.extendedVertices (t+1)) (fun t=>Vort.extendedVertices (t+buffer))
      (fun t=>Vort.extendedIndices (t+1)) (fun t=>Vort.extendedIndices (t+buffer))
      cost deepCost r (i+1) A (Vort.extendedVertices (i+2)) (Vort.extendedVertices (i+1))
      (Vort.extendedIndices (i+2)) (Finset.Icc (i+3-buffer) i) (inner i) (cross i) :=by
  exact ordinary_uniform_protected_balance_history_at Q H
    (fun t=>Vort.extendedVertices (t+1)) (fun t=>Vort.extendedVertices (t+buffer))
    (fun t=>Vort.extendedIndices (t+1)) (fun t=>Vort.extendedIndices (t+buffer))
    cost deepCost r (i+1) L A
    (fun t=>Vort.extendedVertices (t+2)) (fun t=>Vort.extendedVertices (t+1))
    (fun t=>Vort.extendedIndices (t+2)) (fun t=>Finset.Icc (t+3-buffer) t) inner cross h i hi
    (by intro j hj;have hh: j ≤ i:=(Finset.mem_Icc.mp hj).2;omega)
end Oberwolfach
