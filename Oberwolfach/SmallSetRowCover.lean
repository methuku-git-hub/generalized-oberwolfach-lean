module

public import Oberwolfach.OrdinaryRowCoversFromCounts
public import Oberwolfach.SuccessiveRootParameters
public import Oberwolfach.RowCoverUnion

@[expose] public section

/-! A small set of ordinary row roots can be covered with bounded loss
on the fixed outside set. The cap and root-set tolerance precede the
forbidden-degree bound; all numerical margins are proved. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_small_set_row_covers (r:ℕ) (hr:4≤r) (C₀ β κ lam:ℝ)
    (hC₀:0≤C₀) (hβ:0<β) (hκ:0<κ) (hlam:0<lam) :
    ∃ K:ℕ,0<K ∧ ∃ θ:ℝ,0<θ ∧ ∀ d:ℕ,∃ N:ℕ,
      ∀ (V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
      ∀ (Q F:SimpleGraph V) (H:V→U→Prop) (n:ℕ) (x:Fin n→V) (A:Finset V),
      N≤A.card → (n:ℝ)≤θ*A.card → Function.Injective x → (∀ i,x i∉A) →
      (∀ i,Q.neighborFinset (x i)⊆A) →
      let T:=fun i=>Finset.univ.filter (H (x i))
      (∀ i,κ*A.card≤((T i).card:ℝ)) → (∀ i,((T i).card:ℝ)≤C₀*A.card) →
      (∀ i,Q.degree (x i)=2*(T i).card) →
      (∀ a,F.degree a≤d) → (∀ i a,Q.Adj (x i) a → ¬F.Adj (x i) a) →
      (∀ i a,Q.Adj (x i) a → 2*lam*(T i).card≤(((T i).filter (H a)).card:ℝ)) →
      (∀ i u,u∈T i → 4*lam*(T i).card≤(((Q.neighborFinset (x i)).filter (fun a=>H a u)).card:ℝ)) →
      (∀ i,∀ S⊆Q.neighborFinset (x i),∀ J⊆T i,
        lam/16*(T i).card≤(S.card:ℝ) → lam/16*(T i).card≤(J.card:ℝ) →
        2*lam*S.card*J.card≤(bipartiteMatrixCut (fun a u=>if H a u then 1 else 0) S J:ℝ)) →
      (∀ i u,u∈T i → ∀ a,a≠x i → ∀ c,c≠x i →
        β*A.card≤(((A.filter (fun z=>H z u))∩Q.neighborFinset a∩Q.neighborFinset c).card:ℝ)) →
      ∃ C:Fin n→Finset (OrdinaryWheel Q F H r),
        (∀ i,OrdinaryRowCover (C i) (x i) A K) ∧
        (∀ i j,i≠j → Disjoint ((C i).biUnion ordinaryWheelResources) ((C j).biUnion ordinaryWheelResources)) ∧
        (∀ a∈A,(ordinaryWheelRimGraph (Finset.univ.biUnion C)).degree a≤n*(2*(K+1))) ∧
        (∀ a∈A,(Finset.univ.filter (ordinaryPackingSpokes (Finset.univ.biUnion C) a)).card≤n*(K+1)) ∧
        (∀ u,(Finset.univ.filter (fun a=>ordinaryPackingSpokes (Finset.univ.biUnion C) a u)).card≤n*r) := by
  obtain ⟨K,hK,θ,hθ,hparameters⟩:=successive_root_parameters r C₀ β κ lam hC₀ hβ hκ hlam
  refine ⟨K,hK,θ,hθ,?_⟩
  intro d
  obtain ⟨M,hM⟩:=ordinary_row_covers_from_fixed_counts lam hlam d
  obtain ⟨N,hN⟩:=hparameters d M
  refine ⟨N,?_⟩
  intro V U _ _ _ _ Q F H n x A hn hnθ hx hxA hSA T hTlo hThi hbal hF hFx hrow hcol hcut hcount
  have hp (i:Fin n):=hN A.card (T i).card n hn (hTlo i) (hThi i) hnθ
  obtain ⟨C,hC,hcross⟩:=hM V U Q F H r K n hr hK x A hx hxA hSA (β*A.card)
    (fun i=>(hp i).1) hbal hF hFx hrow hcol hcut hcount
    (fun i=>(hp i).2.1) (fun i=>(hp i).2.2.1) (fun i=>(hp i).2.2.2)
  have hd:=row_cover_union_degree_bounds C x A hxA hC
  exact ⟨C,hC,hcross,hd.1,hd.2.1,hd.2.2⟩

end Oberwolfach
