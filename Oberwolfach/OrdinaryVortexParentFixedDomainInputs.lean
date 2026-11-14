module

public import Oberwolfach.OrdinaryTriangleDeepInputsFixedDomain
public import Oberwolfach.MarkedFixedVortexGeometry
public import Oberwolfach.VortexProtectedGeometry

@[expose] public section
/-! The same fixed full-parent domains supply all deterministic inputs to
both all-level triangle and reference-cut probability theorems. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_vortex_parent_fixed_domain_inputs
    (P:SimpleGraph V) (D vsize d:ℕ) (β ε α pstar ω a εTri pR pH:ℝ)
    (Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (hε:0<ε) (L M:ℕ) (hL:L<Q.length) (hM:(M:ℝ)≤ε*vsize/2):
    let W:=markedVortexVertexType Q;let Z:=markedVortexHubType Q
    let f:=fun i=>(markedVortexVertexEmbedding Q i).toEmbedding
    let ρ:=markedVortexPermutation Q π hπ
    let F:=permutationConflictGraph π (3*d)
    let Dlevel:=fun i=>2*(Fintype.card (Z i):ℝ)/initialIndexDensity U D;
    (∀i≤L,OrdinaryDeepCoverLevelInputs 2 (2*(3*d)) d α pstar ω a εTri
      (P.comap (f i)) (F.comap (f i)) (ρ i) (markedVortexInnerHubs Q i) pR pH (Dlevel i) β)→
    (∀i≤L,M≤Fintype.card (W i)) ∧
    (∀i<L,(Fintype.card (W (i+1)):ℝ)≤ε*Fintype.card (W i)) ∧
    (∀i≤L,ω*Fintype.card (W i)≤(Fintype.card (Z i):ℝ) ∧ Fintype.card (Z i)≤Fintype.card (W i)) ∧
    (∀i≤L,∀v,(max (1/2) (cycleThreshold 3)+α)*Fintype.card (W i)≤((P.comap (f i)).degree v:ℝ)) ∧
    (∀i≤L,∀v,((F.comap (f i)).degree v:ℝ)≤2*(3*d)) ∧
    (∀i≤L,permutationConflictGraph (ρ i) (3*d)≤F.comap (f i)) ∧
    (∀i≤L,∀x l,0<l→l<2*d+1→((ρ i)^l) x≠x) ∧
    (∀i≤L,(Fintype.card (W i):ℝ)/2≤Dlevel i) ∧
    (∀i≤L,∀v,|((P.comap (f i)).degree v:ℝ)-Dlevel i|≤εTri*Fintype.card (W i)) ∧
    (∀i≤L,pR*Dlevel i=2*(Fintype.card (Z i):ℝ)*pH) :=by
  intro W Z f ρ F Dlevel hinputs
  have hfields:∀i≤L,ω*Fintype.card (W i)≤(Fintype.card (Z i):ℝ) ∧ Fintype.card (Z i)≤Fintype.card (W i) ∧
      (∀v,(max (1/2) (cycleThreshold 3)+α)*Fintype.card (W i)≤((P.comap (f i)).degree v:ℝ)) ∧
      (∀v,((F.comap (f i)).degree v:ℝ)≤2*(3*d)) ∧ permutationConflictGraph (ρ i) (3*d)≤F.comap (f i) ∧
      (∀x l,0<l→l<2*d+1→((ρ i)^l) x≠x) ∧ (Fintype.card (W i):ℝ)/2≤Dlevel i ∧
      (∀v,|((P.comap (f i)).degree v:ℝ)-Dlevel i|≤εTri*Fintype.card (W i)) ∧
      pR*Dlevel i=2*(Fintype.card (Z i):ℝ)*pH:=by
    intro i hi
    have hh := ordinary_triangle_deep_inputs_fixed_domain (2*(3*d)) d α pstar ω a εTri
      (P.comap (f i)) (F.comap (f i)) (ρ i) (markedVortexInnerHubs Q i) pR pH (Dlevel i) β (hinputs i hi)
    push_cast at hh
    exact hh
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i hi
    have hXi:Fintype.card (W i)=(Q.vertices i).card:=by
      change Fintype.card (Q.extendedVertices i)=(Q.vertices i).card
      rw [Fintype.card_coe,Q.extendedVertices_eq (by omega)]
    have hh:=Q.vertices_lower (i:=i) (by omega)
    have hreal:(M:ℝ)≤Fintype.card (W i):=by rw [hXi];exact hM.trans hh
    exact_mod_cast hreal
  · intro i hi
    have hh:=(Q.extended_successor_size_bounds hε.le i).1
    simpa only [W,markedVortexVertexType,Fintype.card_coe] using hh
  · intro i hi;exact ⟨(hfields i hi).1,(hfields i hi).2.1⟩
  · intro i hi;exact (hfields i hi).2.2.1
  · intro i hi;exact (hfields i hi).2.2.2.1
  · intro i hi;exact (hfields i hi).2.2.2.2.1
  · intro i hi;exact (hfields i hi).2.2.2.2.2.1
  · intro i hi;exact (hfields i hi).2.2.2.2.2.2.1
  · intro i hi;exact (hfields i hi).2.2.2.2.2.2.2.1
  · intro i hi;exact (hfields i hi).2.2.2.2.2.2.2.2
end Oberwolfach
