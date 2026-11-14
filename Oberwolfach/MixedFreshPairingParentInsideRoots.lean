module

public import Oberwolfach.MixedFreshBoundaryPairingsInsideRoots

@[expose] public section
/-! Name the adaptive fresh pairing event and package its fixed parent
    hypotheses for the actual inside-root boundary construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 8000000
set_option synthInstance.maxSize 8192
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W J K E:Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K] [Fintype E] [DecidableEq E]

def MixedFreshPairingAvoidingEvent (m:ℕ) (p ρ ζ:ℝ) (Q F:SimpleGraph V) (P B₀:SimpleGraph W)
    (e:V↪W) (T:J→Finset V) (S U:K→Finset W) (f:J→V↪E) (g:K→W↪E) (σ:E→Bool):Prop:=
  ∀ (Z:SimpleGraph W) (ℓ:ℝ),(∀ w,(Z.degree w:ℝ)≤ℓ)→∀ (Y:J→Finset V) (S' U':K→Finset W),
        (∀ j,Y j⊆T j)→(∀ j,(m+1)∣(Y j).card)→
        (∀ k,S' k⊆S k)→(∀ k,U' k⊆U k)→(∀ k,(S' k).card=2*(U' k).card)→
        (∀ j,(((((T j).filter (fun v=>σ (f j v)=true))\Y j).card+
          (Y j\((T j).filter (fun v=>σ (f j v)=true))).card:ℕ):ℝ)≤ζ*(p*(T j).card))→
        (∀ k,((changed (S' k) ((S k).filter (fun w=>σ (g k w)=true))).card:ℝ)≤ζ*(p*Fintype.card W))→
        (∀ k,((changed (U' k) ((U k).filter (fun w=>σ (g k w)=true))).card:ℝ)≤ζ*(p*Fintype.card W))→
        (∀ i j:J⊕K,i≠j→
          ((Sum.elim (fun j=>(Y j).image e) (fun k=>S' k∪U' k) i∩
            Sum.elim (fun j=>(Y j).image e) (fun k=>S' k∪U' k) j).card:ℝ)≤ρ^2*Fintype.card W)→
        (∀ w,((Finset.univ.filter (fun i:J⊕K=>w∈Sum.elim (fun j=>(Y j).image e) (fun k=>S' k∪U' k) i)).card:ℝ)
          ≤ρ*Fintype.card W)→
        (∀ j,2*(ρ*Real.sqrt ρ*Fintype.card W)+
          2*(Nat.ceil (4*(ρ*Real.sqrt ρ*Fintype.card W)):ℝ)+ℓ≤ζ*(p*(T j).card))→
        (2*(ρ*Real.sqrt ρ*Fintype.card W)+
          2*(Nat.ceil (4*(ρ*Real.sqrt ρ*Fintype.card W)):ℝ)+ℓ≤ζ*(p*Fintype.card W))→
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

structure MixedFreshPairingParentInsideRoots (m b₀:ℕ) (γ κ b B p₀ a ε η:ℝ)
    (Q F:SimpleGraph V) (P B₀:SimpleGraph W) (e:V↪W)
    (T:J→Finset V) (S U:K→Finset W) (t:K→ℝ) where
  mapped_host:Q.map e≤P
  endpoint_disjoint:∀k,Disjoint (S k) (U k)
  hub_size:∀j,κ*Fintype.card V≤((T j).card:ℝ)
  endpoint_size:∀k,a*Fintype.card W≤((S k).card:ℝ) ∧ a*Fintype.card W≤((U k).card:ℝ)
  endpoint_probability:∀k,p₀≤t k ∧ t k≤1
  rim_conflict:∀v,(F.degree v:ℝ)≤ε*Fintype.card V
  physical_conflict:∀w,B₀.degree w≤b₀
  hub_neighborhoods:∀j,∀X:Finset V,X⊆T j→X.card≤2→
    γ*Fintype.card V≤((common (T j) X (fun x=>Q.neighborFinset x)).card:ℝ)
  endpoint_row:∀k v,v∈S k→|(((U k)∩P.neighborFinset v).card:ℝ)-t k*(U k).card|≤η*(U k).card
  endpoint_column:∀k v,v∈U k→|(((S k)∩P.neighborFinset v).card:ℝ)-t k*(S k).card|≤η*(S k).card
  endpoint_codegree:∀k v,v∈S k→∀w,w∈S k→v≠w→¬B₀.Adj v w→
    ((((U k)∩P.neighborFinset v)∩P.neighborFinset w).card:ℝ)≤(t k^2+η)*(U k).card
  hub_weight:∀j,LocalOrdinaryCycle Q F (T j) (m+1)→ℝ
  hub_weight_bounds:∀j C,b/(Fintype.card V:ℝ)^m≤hub_weight j C ∧ hub_weight j C≤B/(Fintype.card V:ℝ)^m
  hub_weight_load:∀j,∀v∈T j,|1-hypergraphWeightedDegree localOrdinaryVertices (hub_weight j) v|≤η

theorem mixed_fresh_pairing_probability_from_inside_parent
    (m:ℕ) (hm:3≤m) (γ κ b B p₀ a:ℝ)
    (hγ:0<γ) (hκ:0<κ) (hb:0<b) (hB:0≤B) (hp₀:0<p₀) (hp₀1:p₀≤1) (ha:0<a) (ha1:a≤1):
    ∃ε η ζ:ℝ,0<ε ∧ 0<η ∧ 0<ζ ∧
    ∀(b₀:ℕ) (p:ℝ) (hp:0<p) (hp1:p≤1) (ρ:ℝ) (hρ:0<ρ) (q:ℕ),∃N:ℕ,
    ∀(V W J K E:Type) [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
      [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K] [Fintype E] [DecidableEq E],
      N≤Fintype.card V→Fintype.card J≤(Fintype.card V)^2→Fintype.card K≤(Fintype.card W)^2→
    ∀(Q F:SimpleGraph V) (P B₀:SimpleGraph W) (e:V↪W)
      (T:J→Finset V) (S U:K→Finset W) (f:J→V↪E) (g:K→W↪E) (t:K→ℝ)
      (data:MixedFreshPairingParentInsideRoots m b₀ γ κ b B p₀ a ε η Q F P B₀ e T S U t),
    1-1/(Fintype.card V:ℝ)^q≤(FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp.le hp1)).probability
      (MixedFreshPairingAvoidingEvent m p ρ ζ Q F P B₀ e T S U f g):=by
  obtain ⟨ε,η,ζ,hε,hη,hζ,hbase⟩:=mixed_fresh_boundary_pairings_inside_roots m hm γ κ b B p₀ a
    hγ hκ hb hB hp₀ hp₀1 ha ha1
  refine ⟨ε,η,ζ,hε,hη,hζ,?_⟩
  intro b₀ p hp hp1 ρ hρ q
  obtain ⟨N,hN⟩:=hbase b₀ p hp hp1 ρ hρ q
  refine ⟨N,?_⟩
  intro V W J K E _ _ _ _ _ _ _ _ _ _ hn hJ hK Q F P B₀ e T S U f g t data
  exact hN V W J K E hn hJ hK Q F P B₀ e data.mapped_host T S U f g t
    data.endpoint_disjoint data.hub_size data.endpoint_size data.endpoint_probability data.rim_conflict
    data.physical_conflict data.hub_neighborhoods data.endpoint_row data.endpoint_column data.endpoint_codegree
    data.hub_weight data.hub_weight_bounds data.hub_weight_load
end Oberwolfach
