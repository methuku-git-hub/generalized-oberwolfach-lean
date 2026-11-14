module

public import Oberwolfach.LongReservedActualFactorPaths
public import Oberwolfach.LongReservedBlockCapacity

@[expose] public section
/-! A floor-free total-length condition implies the reserved path allocation. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_reserved_actual_factor_paths_from_total_length
    {V I J:Type*} [Fintype V] [DecidableEq V] [Fintype I] [Fintype J]
    (G:SimpleGraph V) (hG:G.IsRegularOfDegree 2)
    (components:I↪G.ConnectedComponent) (c d:ℕ) (t:J→ℕ) (ht:∀a,t a≤d)
    (hlarge:∀i:I,c*d+5≤Fintype.card (components i))
    (htotal:2*(c*d+5)*Fintype.card J≤∑i:I,Fintype.card (components i)):
    ∃index:J↪LongReservedBlockIndex G components c d,
    ∃f:∀a:J,Fin (c*t a+5)↪V,
      (∀(a:J) (j:Fin (c*t a+4)),G.Adj
        (f a ⟨j.val,by omega⟩) (f a ⟨j.val+1,by omega⟩)) ∧
      (∀a j,f a j ∈ (components (index a).1).supp) ∧
      (∀a b:J,a≠b→Disjoint (Finset.univ.image (f a)) (Finset.univ.image (f b))) := by
  have hcap:=long_reserved_total_block_capacity (c*d+5) (by omega)
    (fun i:I=>Fintype.card (components i)) hlarge (Fintype.card J) htotal
  exact long_reserved_actual_factor_paths G hG components c d t ht hcap
end Oberwolfach
