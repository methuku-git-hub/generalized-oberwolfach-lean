module

public import Oberwolfach.OrdinaryProtectedCorrectionConflictInner
public import Oberwolfach.VortexExtended

@[expose] public section
/-! All later vortex parent pairs inherit the protected correction edit bound.
The bound depends only on the permutation-conflict radius, not the sample size. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_vortex_correction_conflict_edits
    (P R JQ:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε m)
    (J JH:V→U→Prop) (K:Finset (Sym2 V⊕(V×U))) (π:Equiv.Perm V) (b:ℕ)
    (hJQ:∀v∈Q.extendedVertices 1,∀w∈Q.extendedVertices 1,¬JQ.Adj v w)
    (hJH:∀v u,JH v u→¬(v∈Q.extendedVertices 1 ∧ u∈Q.extendedIndices 1))
    (havoid:Disjoint K (ordinaryRootResources (Q.extendedVertices 1) (Q.extendedIndices 1))):
    let F:=permutationConflictGraph π b;
    let S:=(R\F)\JQ;
    let H:=fun v u=>J v u∧¬JH v u;
    let S₀:=S\ordinaryResourceRim S K;
    let H₀:=fun v u=>H v u∧¬(Sum.inr (v,u)∈K);
    ∀i:ℕ,
      let X:=Q.extendedVertices (i+1);let Z:=Q.extendedIndices (i+1);
      ∀a:↥X⊕↥Z,
      ((changed ((ordinaryPhysicalGraph (R.induce (X:Set V))
        (fun (v:↥X) (u:↥Z)=>J v.val u.val)).neighborFinset a)
        ((ordinaryPhysicalGraph (S₀.induce (X:Set V))
        (fun (v:↥X) (u:↥Z)=>H₀ v.val u.val)).neighborFinset a)).card:ℝ)≤2*(b:ℝ):=by
  intro F S H S₀ H₀ i X Z
  have hX:X⊆Q.extendedVertices 1:=Q.extendedVertices_subset (by omega)
  have hZ:Z⊆Q.extendedIndices 1:=Q.extendedIndices_subset (by omega)
  exact ordinary_protected_correction_conflict_inner R JQ J JH K π b X (Q.extendedVertices 1)
    Z (Q.extendedIndices 1) hX hZ hJQ hJH havoid
end Oberwolfach
