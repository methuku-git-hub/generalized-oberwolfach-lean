module

public import Oberwolfach.OrdinaryFixedVortexDeepCoverInputs
public import Oberwolfach.OrdinaryVortexGeneralParentFixedDomainInputs

@[expose] public section
/-! The original regular-host, vortex and sampling-mean assumptions imply the
full-parent domain inputs simultaneously at all fixed levels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option maxRecDepth 16384
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_vortex_general_parent_inputs_from_original
    (mWheel:ℕ) (hm:2≤mWheel) (P:SimpleGraph V) (D vsize d:ℕ) (β ε α ρ₀ pstar εTri pR pH:ℝ)
    (Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (hreg:P.IsRegularOfDegree D) (hn:0<Fintype.card V)
    (hα:0<α) (hdegree:(max (1/2) (cycleThreshold (mWheel+1))+2*α)*Fintype.card V≤D)
    (hρ₀:0<ρ₀) (hρlo:ρ₀≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (hβ:0≤β) (hβα:β≤α/4) (hβ1:β≤1/4) (hβε:β≤εTri)
    (hε:0<ε) (hε1:ε≤1) (hερ:ε≤ρ₀/16) (hvsize:0<vsize)
    (hnoshort:∀x k,0<k→k<2*d+1→(π^k) x≠x)
    (hpR:pstar≤pR) (hpR1:pR≤1) (hpH:pstar≤pH) (hpH1:pH≤1)
    (hpEq:pR=initialIndexDensity U D*pH)
    (L M:ℕ) (hL:L<Q.length) (hM:(M:ℝ)≤ε*vsize/2):
    let W:=markedVortexVertexType Q;let Z:=markedVortexHubType Q
    let f:=fun i=>(markedVortexVertexEmbedding Q i).toEmbedding
    let ρ:=markedVortexPermutation Q π hπ
    let F:=permutationConflictGraph π (3*d)
    let Dlevel:=fun i=>2*(Fintype.card (Z i):ℝ)/initialIndexDensity U D;
    (∀i≤L,OrdinaryDeepCoverLevelInputs mWheel (2*(3*d)) d α pstar (ρ₀/16) 1 εTri
      (P.comap (f i)) (F.comap (f i)) (ρ i) (markedVortexInnerHubs Q i) pR pH (Dlevel i) β) ∧
    (∀i≤L,M≤Fintype.card (W i)) ∧
    (∀i<L,(Fintype.card (W (i+1)):ℝ)≤ε*Fintype.card (W i)) ∧
    (∀i≤L,(ρ₀/16)*Fintype.card (W i)≤(Fintype.card (Z i):ℝ) ∧ Fintype.card (Z i)≤Fintype.card (W i)) ∧
    (∀i≤L,∀v,(max (1/2) (cycleThreshold (mWheel+1))+α)*Fintype.card (W i)≤((P.comap (f i)).degree v:ℝ)) ∧
    (∀i≤L,∀v,((F.comap (f i)).degree v:ℝ)≤2*(3*d)) ∧
    (∀i≤L,permutationConflictGraph (ρ i) (3*d)≤F.comap (f i)) ∧
    (∀i≤L,∀x l,0<l→l<2*d+1→((ρ i)^l) x≠x) ∧
    (∀i≤L,(Fintype.card (W i):ℝ)/2≤Dlevel i) ∧
    (∀i≤L,∀v,|((P.comap (f i)).degree v:ℝ)-Dlevel i|≤εTri*Fintype.card (W i)) ∧
    (∀i≤L,pR*Dlevel i=2*(Fintype.card (Z i):ℝ)*pH) :=by
  intro W Z f ρ F Dlevel
  have hinputs:∀i≤L,OrdinaryDeepCoverLevelInputs mWheel (2*(3*d)) d α pstar (ρ₀/16) 1 εTri
      (P.comap (f i)) (F.comap (f i)) (ρ i) (markedVortexInnerHubs Q i) pR pH (Dlevel i) β:=by
    intro i hi
    exact ordinary_fixed_vortex_deep_cover_inputs mWheel d P D vsize β ε (max (1/2) (cycleThreshold (mWheel+1)))
      (2*α) α ρ₀ pstar (ρ₀/16) 1 εTri pR pH Q π hπ hreg hn
      (le_max_left _ _) (le_max_right _ _) (by linarith) (by linarith) hdegree
      hρ₀ hρlo hρhi hβ (by linarith) hβ1 hβε hε hε1 (by linarith) hvsize hnoshort
      hpR hpR1 hpH hpH1 hpEq i (by omega)
  exact ⟨hinputs,ordinary_vortex_general_parent_fixed_domain_inputs mWheel hm P D vsize d β ε α pstar (ρ₀/16) 1 εTri pR pH
    Q π hπ hε L M hL hM hinputs⟩
end Oberwolfach
