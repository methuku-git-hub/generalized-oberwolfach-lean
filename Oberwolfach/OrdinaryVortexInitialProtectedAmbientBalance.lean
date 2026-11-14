module

public import Oberwolfach.OrdinaryVortexInitialProtectedBothBalance
public import Oberwolfach.OrdinaryVortexLocalBalanceToAmbient

@[expose] public section
/-! The original protected correction gives both initial local balance
profiles at every later vortex level on the same raw sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 26000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_vortex_initial_protected_ambient_balance
    (P JQ:SimpleGraph V) (JH:V→U→Prop) (D m:ℕ) (β ε θ α pR pH εR εH βe βh η:ℝ)
    (Q:Vortex U P D β ε m) (π:Equiv.Perm V) (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d:ℕ) (s:U→Color→ℝ) (j:Color) (σ:RawWheelOutcome V U Γ Color)
    (hn:0<Fintype.card V) (hreg:P.IsRegularOfDegree D) (hρ:0< initialIndexDensity U D)
    (hβ:0≤β) (hpR:0≤pR) (hpR1:pR≤1) (hpH:0≤pH) (hεR:0≤εR) (hεH:0≤εH)
    (hθ:1/2≤θ) (hβα:β≤2*α) (hdegree:(θ+α)*Fintype.card V≤D)
    (hpEq:pR=initialIndexDensity U D*pH) (hs:∀u,s u j=pH)
    (K:Finset (Sym2 V⊕(V×U)))
    (hJQ:∀v∈Q.extendedVertices 1,∀w∈Q.extendedVertices 1,¬JQ.Adj v w)
    (hJH:∀v u,JH v u→¬(v∈Q.extendedVertices 1 ∧ u∈Q.extendedIndices 1))
    (havoid:Disjoint K (ordinaryRootResources (Q.extendedVertices 1) (Q.extendedIndices 1)))
    (hgood:OrdinaryFixedVortexRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d)) D m β ε Q π hπ pR pH s j σ)
    (i:ℕ) (hi:i+1<Q.length):
    let f:=markedVortexVertexEmbedding Q (i+1);let g:=markedVortexHubEmbedding Q (i+1);
    let ρ:=markedVortexPermutation Q π hπ (i+1);let raw:=ordinaryRawRestrictPair f g σ;
    let F:=permutationConflictGraph π (3*d);let R:=rawWheelGraph P σ;let J:=rawWheelSpokes π d σ j;
    let S:=(R\F)\JQ;let H:=fun v u=>J v u∧¬JH v u;
    let S₀:=S\ordinaryResourceRim S K;let H₀:=fun v u=>H v u∧¬(Sum.inr (v,u)∈K);
    let I:=markedVortexInnerVertices Q (i+1);let B:=markedVortexInnerHubs Q (i+1);let L:=2*((3*d:ℕ):ℝ);
    βe*Fintype.card (markedVortexVertexType Q (i+1)⊕markedVortexHubType Q (i+1))+εR*I.card+3*L≤
      pR^2*pH*(2*(θ+α-β/2)-1)*I.card→
    βh*Fintype.card (markedVortexVertexType Q (i+1)⊕markedVortexHubType Q (i+1))+εH*B.card+2*L≤pH^2*B.card→
    (initialIndexDensity U D*pH)*β*I.card+εR*I.card+2*(εH*B.card)+3*L≤η*I.card→
    OrdinaryCleanupParentProfiles (P.comap f) (S₀.comap f) (F.comap f) (fun v u=>H₀ (f v) (g u)) ρ d I B
      pR pH (θ+α-β/2) (εR*I.card) (εH*B.card) L βe βh (fun u=>s (g u)) j raw ∧
    (∀v:I,|(((S₀.comap f).induce (I:Set _)).degree v:ℝ)-
      2*(Finset.univ.filter (fun u:B=>H₀ (f v.val) (g u.val))).card|≤η*I.card) ∧
    (∀v∉I,|(((S₀.comap f).neighborFinset v∩I).card:ℝ)-2*(B.filter (fun u=>H₀ (f v) (g u))).card|≤η*I.card) ∧
    (∀v∈Q.extendedVertices (i+1+1),|((spanningRestriction S₀ (Q.extendedVertices (i+1+1))).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H₀ v u∧v∈Q.extendedVertices (i+1+1)∧u∈Q.extendedIndices (i+1+1))).card|≤η*I.card) ∧
    (∀v∈Q.extendedVertices (i+1),v∉Q.extendedVertices (i+1+1)→
      |((S₀.neighborFinset v∩Q.extendedVertices (i+1+1)).card:ℝ)-
      2*((Q.extendedIndices (i+1+1)).filter (H₀ v)).card|≤η*I.card) :=by
  intro f g ρ raw F R J S H S₀ H₀ I B L hext hhub hmargin
  have hh:=ordinary_vortex_initial_protected_both_balance P JQ JH D m β ε θ α pR pH εR εH βe βh η
    Q π hπ d s j σ hn hreg hρ hβ hpR hpR1 hpH hεR hεH hθ hβα hdegree hpEq hs K hJQ hJH havoid hgood i hi hext hhub hmargin
  have ht:=ordinary_vortex_local_balance_to_ambient P S₀ H₀ D m β ε Q (i+1) (η*I.card)
    (by convert hh.2.1 using 1 <;> congr! 8 <;> try (apply Finset.ext; intro x; simp) <;> try rfl <;> try (apply congrArg Finset.card; ext u; simp))
    (by convert hh.2.2 using 1 <;> congr! 8 <;> try (apply Finset.ext; intro x; simp) <;> try rfl <;> try (apply congrArg Finset.card; ext u; simp))
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact hh.1
  · exact hh.2.1
  · exact hh.2.2
  · convert ht.1 using 1 <;> congr! 8 <;> try (apply Finset.ext; intro x; simp) <;> try rfl <;> try (apply congrArg Finset.card; ext u; simp)
  · convert ht.2 using 1 <;> congr! 8 <;> try (apply Finset.ext; intro x; simp) <;> try rfl <;> try (apply congrArg Finset.card; ext u; simp)
end Oberwolfach
