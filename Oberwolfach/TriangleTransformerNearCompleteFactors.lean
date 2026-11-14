module

public import Oberwolfach.TriangleTransformerAvailableHubSets

@[expose] public section
/-! The near-complete spoke graph supplies the common-hub available sets
needed for the simultaneous fresh triangle-factor construction. -/
set_option autoImplicit false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem triangular_transformer_factors_from_near_complete_spokes
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
    ∀ (W:Finset V) (ε:ℝ),
    (∀ u,(((Finset.univ:Finset V).filter (fun v=>¬K v u)).card:ℝ)≤ε*(Fintype.card V:ℝ)) →
    2*ε*(Fintype.card V:ℝ)+(W.card:ℝ)≤(β/4)*(Fintype.card V:ℝ) →
    let Z:U→Finset V:=fun u=>(Finset.univ.filter (fun i:{e:V×U // H e.1 e.2}=>i.val.2=u)).biUnion
      (fun i=>(p i).2.2.support.toFinset)
    (∀ i,Z (ι i)⊆W) →
    ∃ S:J→Finset V,
      (∀ i,(S i).card=s ∧ Disjoint (S i) W ∧
        (∀ v∈S i∪Z (ι i),K v (ι i)∧K v (ψ (ι i))) ∧
        TriangleTransformerFactorPair G (S i) (Z (ι i))) ∧
      (∀ i j,i≠j→Disjoint (S i∪Z (ι i)) (S j∪Z (ι j))) := by
  obtain ⟨s₀,hs⟩:=triangular_transformer_fresh_spoke_factors K₀ L β hβ hβ1
  refine ⟨s₀,?_⟩
  intro s hs₀ hdivs
  obtain ⟨N,hN⟩:=hs s hs₀ hdivs
  refine ⟨N,?_⟩
  intro V U J _ _ _ _ _ _ hn hJ ι G Q F H K ψ p hpath hdis hF hH hdiv hsize hdeg W ε hnear hbudget Z hZW
  let A:J→Finset V:=fun i=>((Finset.univ:Finset V).filter (fun v=>K v (ι i)∧K v (ψ (ι i))))\W
  have hA (i:J):
      (∀ v∈A i,K v (ι i)∧K v (ψ (ι i))) ∧ Disjoint (A i) W ∧
      (((Finset.univ:Finset V)\A i).card:ℝ)≤2*ε*(Fintype.card V:ℝ)+(W.card:ℝ):=
    triangular_transformer_common_hub_available K (ι i) (ψ (ι i)) W ε hnear
  have hmiss (i:J):(((Finset.univ:Finset V)\A i).card:ℝ)≤(β/4)*(Fintype.card V:ℝ):=
    (hA i).2.2.trans hbudget
  have hAvoid (i j:J):Disjoint (A i) (Z (ι j)):=(hA i).2.1.mono_right (hZW j)
  obtain ⟨S,hS,hpair⟩:=hN V U J hn hJ ι G Q F H K ψ p hpath hdis hF hH hdiv hsize hdeg A hmiss
    (fun i v hv=>(hA i).1 v hv) hAvoid
  refine ⟨S,?_,hpair⟩
  intro i
  exact ⟨(hS i).1,(hA i).2.1.mono_left (hS i).2.1,(hS i).2.2.2.1,(hS i).2.2.2.2⟩
end Oberwolfach
