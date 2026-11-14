module

public import Oberwolfach.TriangleTransformerAvailableFactors
public import Oberwolfach.OrdinaryTransformerSpokeSets

@[expose] public section
/-! Apply the minimum-degree triangle factor construction to the actual
spoke-path vertex sets of the transformer. The sets of available vertices
may be chosen after previous bounded exclusions. -/
set_option autoImplicit false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem triangular_transformer_spoke_factors
    (L:ℕ) (β:ℝ) (hβ:0<β) (hβ1:β≤1):
    ∃ s₀:ℕ,∀ s:ℕ,s₀≤s → 3∣s → ∃ N:ℕ,
    ∀ (V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
    N≤Fintype.card V → ∀ (G Q F:SimpleGraph V) (H K:V→U→Prop) (ψ:U→U),
    ∀ (p:{e:V×U // H e.1 e.2}→(Σ a:V,Σ b:V,Q.Walk a b)),
    (∀ i,(p i).2.2.IsPath∧(p i).2.2.length=1) →
    (∀ i j,i≠j→Disjoint (p i).2.2.support.toFinset (p j).2.2.support.toFinset) →
    (∀ i j,∀ v∈(p i).2.2.support,∀ w∈(p j).2.2.support,¬F.Adj v w) →
    (∀ i,∀ v∈(p i).2.2.support,K v i.val.2∧K v (ψ i.val.2)) →
    (∀ u,3∣((Finset.univ:Finset V).filter (fun v=>H v u)).card) →
    (∀ u,2*((Finset.univ:Finset V).filter (fun v=>H v u)).card≤L) →
    (∀ v,(3/4+β)*(Fintype.card V:ℝ)≤(G.degree v:ℝ)) →
    ∀ (A:U→Finset V),
    (∀ u,(((Finset.univ:Finset V)\A u).card:ℝ)≤(β/2)*(Fintype.card V:ℝ)) →
    (∀ u v,v∈A u→K v u∧K v (ψ u)) →
    let Z:U→Finset V:=fun u=>(Finset.univ.filter (fun i:{e:V×U // H e.1 e.2}=>i.val.2=u)).biUnion
      (fun i=>(p i).2.2.support.toFinset)
    (∀ u u',u≠u'→Disjoint (Z u) (Z u')) ∧
    ∀ u,∃ S:Finset V,S.card=s ∧ S⊆A u ∧ Disjoint S (Z u) ∧
      (∀ v∈S∪Z u,K v u∧K v (ψ u)) ∧
      ∃ M₁ M₂:Finset (OrdinaryCycle G 3),
        (∀ C∈M₁,∀ D∈M₁,C≠D → Disjoint (ordinaryCycleVertices G 3 C) (ordinaryCycleVertices G 3 D)) ∧
        M₁.biUnion (ordinaryCycleVertices G 3)=S∪Z u ∧
        (∀ C∈M₂,∀ D∈M₂,C≠D → Disjoint (ordinaryCycleVertices G 3 C) (ordinaryCycleVertices G 3 D)) ∧
        M₂.biUnion (ordinaryCycleVertices G 3)=S ∧
        (∀ C∈M₁,∀ D∈M₂,Disjoint C.val.val.edgeFinset D.val.val.edgeFinset) ∧
        (∀ C∈M₁,∀ v w,C.val.val.Adj v w → v∈S ∨ w∈S) := by
  obtain ⟨s₀,hs⟩:=triangle_transformer_available_sample_factors L β hβ hβ1
  refine ⟨s₀,?_⟩
  intro s hs₀ hdivs
  obtain ⟨N,hN⟩:=hs s hs₀ hdivs
  refine ⟨N,?_⟩
  intro V U _ _ _ _ hn G Q F H K ψ p hpath hdis hF hH hdiv hsize hdeg A hmiss hcommon Z
  have hsets:=ordinary_transformer_spoke_sets Q F H K ψ 3 (by omega) p
    (by intro i;simpa using hpath i) hdis hF hH hdiv
  dsimp only at hsets
  refine ⟨hsets.2.2.1,?_⟩
  intro u
  have hz:(Z u).card≤L:=by
    rw [hsets.1 u]
    simpa using hsize u
  obtain ⟨S,hSc,hSA,hSZ,M₁,M₂,hp₁,hc₁,hp₂,hc₂,hcross,hold⟩:=
    hN V hn G (A u) (Z u) hz (hsets.2.1 u) hdeg (hmiss u)
  refine ⟨S,hSc,hSA,hSZ,?_,M₁,M₂,hp₁,hc₁,hp₂,hc₂,hcross,hold⟩
  intro v hv
  rcases Finset.mem_union.mp hv with hv|hv
  · exact hcommon u v (hSA hv)
  · exact hsets.2.2.2.1 u v hv
end Oberwolfach
