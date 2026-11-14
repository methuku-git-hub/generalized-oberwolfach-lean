module

public import Oberwolfach.MarkedFixedVortexParentDegrees
public import Oberwolfach.SuccessorWeightFamilies

@[expose] public section
/-! Successor weights on the actual fixed vortex subtypes. The entire family
is selected before the sampling densities and outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_fixed_vortex_successor_weight_families
    (k c:ℕ) (hlen:c+1=(k+2)*2) (α τ:ℝ) (hα:0<α) (hτ:0<τ)
    (hmargin:successorCycleRatio k+α/4≤1/2+α/2):
    ∃ βmax:ℝ,0<βmax ∧ ∀ b:ℕ,∃ N:ℕ,1≤N ∧
    ∀ (V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U G D β ε m),
    G.IsRegularOfDegree D→0<Fintype.card V→
    (1/2+α)*Fintype.card V≤(D:ℝ)→0 < initialIndexDensity U D→
    0≤β→β≤βmax→0<ε→(N:ℝ)≤ε*m/2→
    ∀ (π:Equiv.Perm V) (hpres:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (L:ℕ),L<Q.length→
    let W:=markedVortexVertexType Q
    let Z:=markedVortexHubType Q
    let f:=markedVortexVertexEmbedding Q
    let ρ:=markedVortexPermutation Q π hpres
    let Dload:=fun i=>2*(Fintype.card (Z i):ℝ)/initialIndexDensity U D
    ∃ weight:∀ i,(Fin (c+1)→W i)→ℝ,
      ∀ i≤L,SuccessorSequenceWeightConditions (G.comap (f i)) (ρ i) b (Dload i) τ
        (successorWeightLower k (α/4)) (successorWeightUpper k (α/4)) (weight i):=by
  obtain ⟨δ,hδ,hbase⟩:=successor_sequence_weight_families k c hlen (α/4) τ (by positivity) hτ
  let βmax:=min (α/8) (min (1/4) δ)
  have hbmax:0<βmax:=by dsimp [βmax];positivity
  refine ⟨βmax,hbmax,?_⟩
  intro b
  obtain ⟨N,hN,hbase⟩:=hbase b
  refine ⟨N,hN,?_⟩
  intro V U _ _ _ _ G D m β ε Q hreg hn hD hρ hb hβmax he hsize π hpres L hL W Z f ρ Dload
  have hbα:β≤α/8:=hβmax.trans (min_le_left _ _)
  have hb1:β≤1/4:=hβmax.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hbδ:β≤δ:=hβmax.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hm:0<m:=by
    by_contra h
    have hm0:m=0:=by omega
    rw [hm0] at hsize
    have hNp:(0:ℝ)<N:=by exact_mod_cast hN
    simp at hsize
    linarith
  have hW (i:ℕ) (hi:i≤L):N≤Fintype.card (W i):=by
    have h0:Fintype.card (W i)=(Q.vertices i).card:=by
      change Fintype.card (Q.extendedVertices i)=(Q.vertices i).card
      rw [Fintype.card_coe,Q.extendedVertices_eq (by omega : i≤Q.length)]
    rw [h0]
    exact_mod_cast hsize.trans (Q.vertices_lower (by omega : i≤Q.length))
  have hfields (i:ℕ) (hi:i≤L):=marked_vortex_fixed_parent_degree_fields Q hreg hn hD hα hρ hb hbα hb1 he hm i (by omega)
  apply hbase W (fun i=>G.comap (f i)) ρ Dload L hW
  · intro i hi
    exact (hfields i hi).2.2.1
  · intro i hi
    exact (hfields i hi).2.2.2
  · intro i hi v
    apply ((hfields i hi).2.1 v).trans
    exact mul_le_mul_of_nonneg_right hbδ (Nat.cast_nonneg _)
  · intro i hi v
    apply le_trans _ ((hfields i hi).1 v)
    exact mul_le_mul_of_nonneg_right hmargin (Nat.cast_nonneg _)
end Oberwolfach
