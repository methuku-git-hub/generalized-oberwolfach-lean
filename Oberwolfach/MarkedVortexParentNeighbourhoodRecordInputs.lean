module

public import Oberwolfach.MarkedParentNeighbourhoodRecordInputs
public import Oberwolfach.MarkedJointActualReferenceAllLevelsParentAgreementWithWeights

@[expose] public section
/-! The common-outcome full-parent estimates supply the four neighbourhood
and retained-spoke agreement fields at every actual vortex level. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]

theorem marked_vortex_parent_neighbourhood_record_inputs
    (r d:ℕ) (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hpres:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V) (hD:0<D)
    (hρhi:initialIndexDensity U D≤1) (he:0≤ε) (L:ℕ) (hL:L<Q.length)
    (p k tol ζ κ:ℝ) (he0:0≤tol+(r+12:ℕ)*ζ)
    (heκ:tol+(r+12:ℕ)*ζ≤κ/4) (hζκ:ζ≤κ/4)
    (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (hfull:∀ i≤L,
      let W:=markedVortexVertexType Q i; let Z:=markedVortexHubType Q i
      let f:=markedVortexVertexEmbedding Q i; let g:=markedVortexHubEmbedding Q i
      let ρ:=markedVortexPermutation Q π hpres i; let σ:=rawMarkedRestrictPair f g z.1
      let H:=fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f x) (g u);
      MarkedRowsWithSpokes (G.comap f) ρ d (r+12) Finset.univ p k (fun u=>q (g u)) (fun u=>s (g u)) a j
        ((tol+(r+12:ℕ)*ζ)*Fintype.card W) σ H ∧
      MarkedIndicesWithSpokes ρ d (r+12) Finset.univ (fun u=>q (g u)) (fun u=>s (g u)) a j
        ((tol+(r+12:ℕ)*ζ)*Fintype.card Z) σ H)
    (hagree:∀ i≤L,
      let W:=markedVortexVertexType Q i; let Z:=markedVortexHubType Q i
      let f:=markedVortexVertexEmbedding Q i; let g:=markedVortexHubEmbedding Q i
      let ρ:=markedVortexPermutation Q π hpres i; let σ:=rawMarkedRestrictPair f g z.1
      let H:=fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f x) (g u);
      (∀ b x,(∑ u,if ¬(rawMarkedPairSpokes ρ d σ a j b x u↔H b x u) then (1:ℝ) else 0)≤ζ*Fintype.card Z) ∧
      (∀ b u,(∑ x,if ¬(rawMarkedPairSpokes ρ d σ a j b x u↔H b x u) then (1:ℝ) else 0)≤ζ*Fintype.card W)):
    ∀ i≤L,
      let W:=markedVortexVertexType Q i; let Z:=markedVortexHubType Q i
      let f:=markedVortexVertexEmbedding Q i; let g:=markedVortexHubEmbedding Q i
      let ρ:=markedVortexPermutation Q π hpres i; let σ:=rawMarkedRestrictPair f g z.1
      let H:=fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f x) (g u);
      MarkedRowsWithSpokes (G.comap f) ρ d (r+12) Finset.univ p k (fun u=>q (g u)) (fun u=>s (g u)) a j ((κ/4)*Fintype.card W) σ H ∧
      MarkedIndicesWithSpokes ρ d (r+12) Finset.univ (fun u=>q (g u)) (fun u=>s (g u)) a j ((κ/4)*Fintype.card W) σ H ∧
      (∀ b x,(∑ u,if ¬(rawMarkedPairSpokes ρ d σ a j b x u↔H b x u) then (1:ℝ) else 0)≤(κ/4)*Fintype.card Z) ∧
      (∀ b u,(∑ x,if ¬(rawMarkedPairSpokes ρ d σ a j b x u↔H b x u) then (1:ℝ) else 0)≤(κ/4)*Fintype.card W):=by
  intro i hi W Z f g ρ σ H
  have hUV:Fintype.card Z≤Fintype.card W:=by
    have hh:=Q.index_size_upper hreg hn hD he hρhi (i:=i) (by omega)
    change Fintype.card ↥(Q.extendedIndices i)≤Fintype.card ↥(Q.extendedVertices i)
    simp only [Fintype.card_coe]
    rw [Q.extendedIndices_eq (by omega:i≤Q.length),Q.extendedVertices_eq (by omega:i≤Q.length)]
    omega
  exact marked_parent_neighbourhood_record_inputs (G.comap f) ρ d (r+12) p k (fun u=>q (g u)) (fun u=>s (g u)) a j
    (tol+(r+12:ℕ)*ζ) ζ κ he0 heκ hζκ hUV σ H (hfull i hi).1 (hfull i hi).2 (hagree i hi).1 (hagree i hi).2
end Oberwolfach
