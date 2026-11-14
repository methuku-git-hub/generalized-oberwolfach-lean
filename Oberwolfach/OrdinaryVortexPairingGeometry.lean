module

public import Oberwolfach.OrdinaryFixedVortexCleanupDomainGeometry
public import Oberwolfach.OrdinaryFixedVortexConflictDegree

@[expose] public section
/-! Original vortex geometry supplies the domain ratios and the fixed
    conflict bound needed by the general pairing parent. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 16384
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_pairing_geometry
    (β ε ρ₀ Kdom εf:ℝ) (d:ℕ)
    (hβ:0≤β) (hβ1:β≤1/4) (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀) (hεf:0<εf)
    (hKdom:1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom):
    ∃v₀:ℕ,1≤v₀ ∧ ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [LinearOrder U]
      (P:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤vsize→
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),∀i,i<Q.length→
    let f:=markedVortexVertexEmbedding Q i;let I:=markedVortexInnerVertices Q i;let B:=markedVortexInnerHubs Q i;
    let Floc:=(permutationConflictGraph π (3*d)).comap f;
    I.Nonempty ∧ (Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i):ℝ)≤(2*Kdom)*I.card ∧
    (ρ₀/8)*(I.card:ℝ)≤B.card ∧ B.card≤I.card ∧
    (∀v,Floc.degree v≤2*(3*d)) ∧
    ((2*(3*d):ℕ):ℝ)≤εf*Fintype.card (markedVortexVertexType Q i) :=by
  have hK1:1≤Kdom:=by
    have h1:0≤1/(ε/2):=by positivity
    have h2:0≤1/((ε/2)*(ρ₀/8)):=by positivity
    linarith only [hKdom,h1,h2]
  obtain ⟨N,hN⟩:=exists_nat_ge (((2*(3*d):ℕ):ℝ)/εf)
  let M:=max N 1
  obtain ⟨v₀,hv₀,hsize⟩:=marked_fixed_vortex_event_size_inputs β ε ρ₀ hβ hβ1 hε hε1 hρ₀ M
  obtain ⟨v₁,hv₁,hgeom⟩:=ordinary_fixed_vortex_cleanup_domain_geometry β ε ρ₀ hβ hβ1 hε hε1 hρ₀ M
  refine ⟨max v₀ v₁,by omega,?_⟩
  intro V U _ _ _ _ P D vsize hreg hn hD hρlo hρhi hv Q π hπ i hi f I B Floc
  have hs:=hsize V U P D vsize hreg hn hD hρlo hρhi (by omega) Q i hi
  have hg:=hgeom V U P D vsize hreg hn hD hρlo hρhi (by omega) Q i hi
  have hI:M≤I.card:=hg.2.2.1
  have hIpos:0<I.card:=by dsimp [M] at hI;omega
  have hIr:(0:ℝ)<I.card:=by exact_mod_cast hIpos
  have hW:(Fintype.card (markedVortexVertexType Q i):ℝ)≤Kdom*I.card:=by
    have hh:=hs.2.2.2.1
    exact hh.trans (mul_le_mul_of_nonneg_right hKdom hIr.le)
  have hUW:Fintype.card (markedVortexHubType Q i)≤Fintype.card (markedVortexVertexType Q i):=
    (marked_vortex_fixed_ambient_size_fields Q hreg hn hD hρ₀ hρlo hρhi hβ hβ1 hε (by omega) i hi).2.2
  have hphysical:(Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i):ℝ)≤(2*Kdom)*I.card:=by
    simp only [Fintype.card_sum,Nat.cast_add]
    have hu:(Fintype.card (markedVortexHubType Q i):ℝ)≤Fintype.card (markedVortexVertexType Q i):=by exact_mod_cast hUW
    nlinarith only [hW,hu]
  have hIle:(I.card:ℝ)≤Fintype.card (markedVortexVertexType Q i):=by exact_mod_cast Finset.card_le_univ I
  have hNI:(N:ℝ)≤I.card:=by exact_mod_cast (show N≤I.card by dsimp [M] at hI;omega)
  have hbound:((2*(3*d):ℕ):ℝ)≤εf*Fintype.card (markedVortexVertexType Q i):=by
    have hh:((2*(3*d):ℕ):ℝ)/εf≤(Fintype.card (markedVortexVertexType Q i):ℝ):=hN.trans (hNI.trans hIle)
    simpa only [mul_comm] using (div_le_iff₀ hεf).mp hh
  refine ⟨Finset.card_pos.mp hIpos,hphysical,hg.2.2.2.2.1,hg.2.2.2.2.2.1,?_,hbound⟩
  intro v
  exact ordinary_fixed_vortex_conflict_degree P D vsize β ε Q π hπ i (3*d) v
end Oberwolfach
