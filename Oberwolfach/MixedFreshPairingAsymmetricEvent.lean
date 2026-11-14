module

public import Oberwolfach.MixedFreshPairingParentInsideRoots

@[expose] public section
/-! Separate inner-scale tolerances for hub factors and endpoint pairings. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W J K E:Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K] [Fintype E] [DecidableEq E]

def MixedFreshPairingAsymmetricEvent (m:ℕ) (p ρ ζh ζe n:ℝ) (Q F:SimpleGraph V) (P B₀:SimpleGraph W)
    (e:V↪W) (T:J→Finset V) (S U:K→Finset W) (f:J→V↪E) (g:K→W↪E) (σ:E→Bool):Prop:=
  ∀ (Z:SimpleGraph W) (ℓ:ℝ),(∀ w,(Z.degree w:ℝ)≤ℓ)→∀ (Y:J→Finset V) (S' U':K→Finset W),
        (∀ j,Y j⊆T j)→(∀ j,(m+1)∣(Y j).card)→
        (∀ k,S' k⊆S k)→(∀ k,U' k⊆U k)→(∀ k,(S' k).card=2*(U' k).card)→
        (∀ j,(((((T j).filter (fun v=>σ (f j v)=true))\Y j).card+
          (Y j\((T j).filter (fun v=>σ (f j v)=true))).card:ℕ):ℝ)≤ζh*(p*(T j).card))→
        (∀ k,((changed (S' k) ((S k).filter (fun w=>σ (g k w)=true))).card:ℝ)≤ζe*(p*n))→
        (∀ k,((changed (U' k) ((U k).filter (fun w=>σ (g k w)=true))).card:ℝ)≤ζe*(p*n))→
        (∀ i j:J⊕K,i≠j→
          ((Sum.elim (fun j=>(Y j).image e) (fun k=>S' k∪U' k) i∩
            Sum.elim (fun j=>(Y j).image e) (fun k=>S' k∪U' k) j).card:ℝ)≤ρ^2*Fintype.card W)→
        (∀ w,((Finset.univ.filter (fun i:J⊕K=>w∈Sum.elim (fun j=>(Y j).image e) (fun k=>S' k∪U' k) i)).card:ℝ)
          ≤ρ*Fintype.card W)→
        (∀ j,2*(ρ*Real.sqrt ρ*Fintype.card W)+
          2*(Nat.ceil (4*(ρ*Real.sqrt ρ*Fintype.card W)):ℝ)+ℓ≤ζh*(p*(T j).card))→
        (2*(ρ*Real.sqrt ρ*Fintype.card W)+
          2*(Nat.ceil (4*(ρ*Real.sqrt ρ*Fintype.card W)):ℝ)+ℓ≤ζe*(p*n))→
        ∃ D:∀ j,Finset (LocalOrdinaryCycle Q F (T j) (m+1)),
        ∃ C:∀ k,EndpointPairing P B₀ (S' k) (U' k),
          (∀ j,(∀ A∈D j,∀ A'∈D j,A≠A'→Disjoint (localOrdinaryVertices A) (localOrdinaryVertices A')) ∧
            (D j).biUnion localOrdinaryVertices=Y j) ∧
          let G:J⊕K→SimpleGraph W:=Sum.elim
            (fun j=>(localOrdinaryFactorGraph (D j)).map e) (fun k=>(C k).graph)
          (∀ i,G i≤spanningRestriction P (Sum.elim (fun j=>(Y j).image e) (fun k=>S' k∪U' k) i)) ∧
          (∀ i j,i≠j→Disjoint (G i) (G j)) ∧
          (∀ i,Disjoint (G i) Z) ∧
          ∀ w,((⨆ i,G i).degree w:ℝ)≤2*(ρ*Fintype.card W)

end Oberwolfach
