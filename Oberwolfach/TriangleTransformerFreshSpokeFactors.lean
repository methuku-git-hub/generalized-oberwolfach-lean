module

public import Oberwolfach.TriangleSimultaneousFreshFactors
public import Oberwolfach.OrdinaryTransformerSpokeSets

@[expose] public section
/-! Actual old spoke-path sets and disjoint new triangle-factor domains
for the bounded family of transformer hubs. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem triangular_transformer_fresh_spoke_factors
    (K₀ L:ℕ) (β:ℝ) (hβ:0<β) (hβ1:β≤1):
    ∃ s₀:ℕ,∀ s:ℕ,s₀≤s → 3∣s → ∃ N:ℕ,
    ∀ (V U J:Type) [Fintype V] [Fintype U] [Fintype J] [DecidableEq V] [DecidableEq U] [DecidableEq J],
    N≤Fintype.card V → Fintype.card J≤K₀ → ∀ (ι:J↪U),
    ∀ (G Q F:SimpleGraph V) (H K:V→U→Prop) (ψ:U→U),
    ∀ (p:{e:V×U // H e.1 e.2}→(Σ a:V,Σ b:V,Q.Walk a b)),
    (∀ i,(p i).2.2.IsPath∧(p i).2.2.length=1) →
    (∀ i j,i≠j→Disjoint (p i).2.2.support.toFinset (p j).2.2.support.toFinset) →
    (∀ i j,∀ v∈(p i).2.2.support,∀ w∈(p j).2.2.support,¬F.Adj v w) →
    (∀ i,∀ v∈(p i).2.2.support,K v i.val.2∧K v (ψ i.val.2)) →
    (∀ u,3∣((Finset.univ:Finset V).filter (fun v=>H v u)).card) →
    (∀ u,2*((Finset.univ:Finset V).filter (fun v=>H v u)).card≤L) →
    (∀ v,(3/4+β)*(Fintype.card V:ℝ)≤(G.degree v:ℝ)) →
    ∀ (A:J→Finset V),
    (∀ i,(((Finset.univ:Finset V)\A i).card:ℝ)≤(β/4)*(Fintype.card V:ℝ)) →
    (∀ i v,v∈A i→K v (ι i)∧K v (ψ (ι i))) →
    let Z:U→Finset V:=fun u=>(Finset.univ.filter (fun i:{e:V×U // H e.1 e.2}=>i.val.2=u)).biUnion
      (fun i=>(p i).2.2.support.toFinset)
    (∀ i j,Disjoint (A i) (Z (ι j))) →
    ∃ S:J→Finset V,
      (∀ i,(S i).card=s ∧ S i⊆A i ∧ Disjoint (S i) (Z (ι i)) ∧
        (∀ v∈S i∪Z (ι i),K v (ι i)∧K v (ψ (ι i))) ∧
        TriangleTransformerFactorPair G (S i) (Z (ι i))) ∧
      (∀ i j,i≠j→Disjoint (S i∪Z (ι i)) (S j∪Z (ι j))) := by
  obtain ⟨s₀,hs⟩:=triangle_transformer_simultaneous_fresh_factors K₀ L β hβ hβ1
  refine ⟨s₀,?_⟩
  intro s hs₀ hdivs
  obtain ⟨N,hN⟩:=hs s hs₀ hdivs
  refine ⟨N,?_⟩
  intro V U J _ _ _ _ _ _ hn hJ ι G Q F H K ψ p hpath hdis hF hH hdiv hsize hdeg A hmiss hcommon Z hAvoid
  have hsets:=ordinary_transformer_spoke_sets Q F H K ψ 3 (by omega) p
    (by intro i;simpa using hpath i) hdis hF hH hdiv
  dsimp only at hsets
  have hZ (i:J):(Z (ι i)).card≤L ∧ 3∣(Z (ι i)).card:=by
    refine ⟨?_,hsets.2.1 (ι i)⟩
    rw [hsets.1 (ι i)]
    simpa using hsize (ι i)
  obtain ⟨S,hS,hpair⟩:=hN V J hn hJ G A (fun i=>Z (ι i)) hdeg hZ hmiss
  refine ⟨S,?_,?_⟩
  · intro i
    refine ⟨(hS i).1,(hS i).2.1,(hS i).2.2.1,?_,(hS i).2.2.2⟩
    intro v hv
    rcases Finset.mem_union.mp hv with hv|hv
    · exact hcommon i v ((hS i).2.1 hv)
    · exact hsets.2.2.2.1 (ι i) v hv
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro v hvi hvj
    rcases Finset.mem_union.mp hvi with hSi|hZi <;> rcases Finset.mem_union.mp hvj with hSj|hZj
    · exact Finset.disjoint_left.mp (hpair i j hij) hSi hSj
    · exact Finset.disjoint_left.mp (hAvoid i j) ((hS i).2.1 hSi) hZj
    · exact Finset.disjoint_left.mp (hAvoid j i) ((hS j).2.1 hSj) hZi
    · exact Finset.disjoint_left.mp (hsets.2.2.1 (ι i) (ι j) (fun h=>hij (ι.injective h))) hZi hZj
end Oberwolfach
