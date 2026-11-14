module

public import Oberwolfach.MixedFreshBoundaryFactorsAvoiding

@[expose] public section
/-! A named event for the mixed fresh boundary factors. Its quantified
physical deletion may be chosen after seeing the sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W J K E:Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K] [Fintype E] [DecidableEq E]

def MixedFreshBoundaryAvoidingEvent (p ρ ζ:ℝ) (Q F:SimpleGraph V) (P B₀:SimpleGraph W)
    (e:V↪W) (T:J→Finset V) (S U:K→Finset W) (f:J→V↪E) (g:K→W↪E)
    (hSU:∀ k,Disjoint (S k) (U k)) (σ:E→Bool):Prop:=
  ∀ (Y:J→Finset V) (Z:K→Finset W) (K₀:SimpleGraph W) (δ:ℝ),
        (∀w,(K₀.degree w:ℝ)≤δ)→
        (∀ j,Y j⊆T j)→(∀ j,3∣(Y j).card)→
        (∀ k,Z k⊆S k∪U k)→(∀ k,(Z k∩S k).card=2*(Z k∩U k).card)→
        (∀ j,(((((T j).filter (fun v=>σ (f j v)=true))\Y j).card+
          (Y j\((T j).filter (fun v=>σ (f j v)=true))).card:ℕ):ℝ)≤ζ*(p*(T j).card))→
        (∀ k,(((((S k∪U k).filter (fun w=>σ (g k w)=true))\Z k).card+
          (Z k\((S k∪U k).filter (fun w=>σ (g k w)=true))).card:ℕ):ℝ)≤ζ*(p*(U k).card))→
        (∀ i j:J⊕K,i≠j→
          ((Sum.elim (fun j=>(Y j).image e) Z i∩Sum.elim (fun j=>(Y j).image e) Z j).card:ℝ)
            ≤ρ^2*Fintype.card W)→
        (∀ w,((Finset.univ.filter (fun i:J⊕K=>w∈Sum.elim (fun j=>(Y j).image e) Z i)).card:ℝ)
          ≤ρ*Fintype.card W)→
        (∀ j,2*(ρ*Real.sqrt ρ*Fintype.card W)+
          2*(Nat.ceil (4*(ρ*Real.sqrt ρ*Fintype.card W)):ℝ)+δ≤ζ*(p*(T j).card))→
        (∀ k,2*(ρ*Real.sqrt ρ*Fintype.card W)+
          2*(Nat.ceil (4*(ρ*Real.sqrt ρ*Fintype.card W)):ℝ)+δ≤ζ*(p*(U k).card))→
        ∃ D:∀ j,Finset (LocalOrdinaryCycle Q F (T j) 3),
        ∃ C:∀ k,Finset (EndpointTriangle P B₀ (S k) (U k)),
          (∀ j,(∀ A∈D j,∀ A'∈D j,A≠A'→Disjoint (localOrdinaryVertices A) (localOrdinaryVertices A')) ∧
            (D j).biUnion localOrdinaryVertices=Y j) ∧
          (∀ k,(∀ A∈C k,∀ A'∈C k,A≠A'→Disjoint (endpointTriangleVertices A) (endpointTriangleVertices A')) ∧
            (C k).biUnion endpointTriangleVertices=Z k) ∧
          let G:J⊕K→SimpleGraph W:=Sum.elim
            (fun j=>(localOrdinaryFactorGraph (D j)).map e) (fun k=>endpointFactorGraph (hSU k) (C k))
          (∀ i,G i≤spanningRestriction P (Sum.elim (fun j=>(Y j).image e) Z i)) ∧
          (∀ i j,i≠j→Disjoint (G i) (G j)) ∧
          (∀ i,Disjoint (G i) K₀) ∧
          ∀ w,((⨆ i,G i).degree w:ℝ)≤2*(ρ*Fintype.card W)
end Oberwolfach
