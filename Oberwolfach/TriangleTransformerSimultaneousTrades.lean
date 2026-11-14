module

public import Oberwolfach.TriangleHubTradesSimultaneous

@[expose] public section
/-! Simultaneous hub-switch decompositions with pairwise disjoint rim and
spoke resources, from the near-complete transformer host. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem triangular_transformer_simultaneous_wheel_trades
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
    (∀ i,ι i≠ψ (ι i)) →
    ∃ (S:J→Finset V) (R:J→SimpleGraph V),
      (∀ i,(S i).card=s ∧ Disjoint (S i) W ∧
        (∀ v∈S i∪Z (ι i),K v (ι i)∧K v (ψ (ι i))) ∧
        TriangleHubTradeAt G K (S i) (Z (ι i)) (ι i) (ψ (ι i)) (R i)) ∧
      (∀ i j,i≠j→Disjoint (S i∪Z (ι i)) (S j∪Z (ι j))) ∧
      (∀ i j,i≠j→Disjoint (R i) (R j)) ∧
      let Sp:J→V→U→Prop:=fun i v z=>(v∈S i∪Z (ι i)∧z=ι i)∨(v∈S i∧z=ψ (ι i))
      let Sm:J→V→U→Prop:=fun i v z=>(v∈S i∪Z (ι i)∧z=ψ (ι i))∨(v∈S i∧z=ι i)
      ∀ i j,i≠j→∀ v z,¬(Sp i v z∧Sp j v z) ∧ ¬(Sm i v z∧Sm j v z) := by
  obtain ⟨s₀,hs⟩:=triangular_transformer_wheel_trades_from_near_complete_spokes K₀ L β hβ hβ1
  refine ⟨s₀,?_⟩
  intro s hs₀ hdivs
  obtain ⟨N,hN⟩:=hs s hs₀ hdivs
  refine ⟨N,?_⟩
  intro V U J _ _ _ _ _ _ hn hJ ι G Q F H K ψ p hpath hdis hF hH hdiv hsize hdeg W ε hnear hbudget Z hZW hdistinct
  obtain ⟨S,hS,hpair⟩:=hN V U J hn hJ ι G Q F H K ψ p hpath hdis hF hH hdiv hsize hdeg W ε hnear hbudget hZW hdistinct
  obtain ⟨R,hR,hRdis,hspoke⟩:=triangle_hub_trades_choose_simultaneously G K S (fun i=>Z (ι i))
    (fun i=>ι i) (fun i=>ψ (ι i)) hpair (fun i=>(hS i).2.2.2)
  exact ⟨S,R,fun i=>⟨(hS i).1,(hS i).2.1,(hS i).2.2.1,hR i⟩,hpair,hRdis,hspoke⟩
end Oberwolfach
