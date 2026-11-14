module

public import Oberwolfach.MixedBoundaryFactorsAvoiding
public import Oberwolfach.OrdinaryFreshTriangleDomainsInsideRoots
public import Oberwolfach.EndpointFreshDomainsQuadraticEvent
public import Oberwolfach.GoodPlacementEvents

@[expose] public section

/-! On one physical-coordinate event, construct the hub and triangle
endpoint factors together, including all permitted later class changes.
The factors are mutually edge-disjoint across both kinds of outside roots. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 6500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem mixed_fresh_boundary_factors_inside_roots (γ κ b B:ℝ) (hγ:0<γ) (hκ:0<κ) (hb:0<b) (hB:0≤B):
    ∃ ε η ζ:ℝ,0<ε ∧ 0<η ∧ 0<ζ ∧
    ∀ (p:ℝ) (hp:0<p) (hp1:p≤1) (ρ:ℝ) (hρ:0<ρ) (q:ℕ),∃ N:ℕ,
    ∀ (V W J K E:Type) [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
      [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K] [Fintype E] [DecidableEq E],
      N≤Fintype.card V→Fintype.card J≤(Fintype.card V)^2→Fintype.card K≤(Fintype.card W)^2→
    ∀ (Q F:SimpleGraph V) (P B₀:SimpleGraph W) (e:V↪W),Q.map e≤P→
    ∀ (T:J→Finset V) (S U:K→Finset W) (f:J→V↪E) (g:K→W↪E)
      (hSU:∀ k,Disjoint (S k) (U k)),
      (∀ j,κ*Fintype.card V≤((T j).card:ℝ))→
      (∀ v,(F.degree v:ℝ)≤ε*Fintype.card V)→
      (∀ w,(B₀.degree w:ℝ)≤ε*Fintype.card W)→
      (∀ j,∀ X:Finset V,X⊆T j→X.card≤3→
        γ*Fintype.card V≤((common (T j) X (fun x=>Q.neighborFinset x)).card:ℝ))→
      (∀ k,EndpointNeighbourCounts P B₀ (S k) (U k) (γ*Fintype.card W))→
    ∀ (wt:∀ j,LocalOrdinaryCycle Q F (T j) 3→ℝ)
      (we:∀ k,EndpointTriangle P B₀ (S k) (U k)→ℝ),
      (∀ j C,b/(Fintype.card V:ℝ)^2≤wt j C ∧ wt j C≤B/(Fintype.card V:ℝ)^2)→
      (∀ k C,b/(Fintype.card W:ℝ)^2≤we k C ∧ we k C≤B/(Fintype.card W:ℝ)^2)→
      (∀ j,∀ v∈T j,|1-hypergraphWeightedDegree localOrdinaryVertices (wt j) v|≤η)→
      (∀ k,∀ w∈S k∪U k,|1-hypergraphWeightedDegree endpointTriangleVertices (we k) w|≤η)→
    1-1/(Fintype.card V:ℝ)^q≤
      (FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp.le hp1)).probability
      (fun σ=>∀ (Y:J→Finset V) (Z:K→Finset W) (K₀:SimpleGraph W) (δ:ℝ),
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
          ∀ w,((⨆ i,G i).degree w:ℝ)≤2*(ρ*Fintype.card W)):=by
  obtain ⟨εo,ηo,ζo,hεo,hηo,hζo,ho⟩:=ordinary_fresh_triangle_domains_inside_roots γ κ b B hγ hκ hb hB
  obtain ⟨εe,ηe,ζe,hεe,hηe,hζe,he⟩:=endpoint_fresh_domains_quadratic_event γ b B hγ hb hB
  refine ⟨min εo εe,min ηo ηe,min ζo ζe,lt_min hεo hεe,lt_min hηo hηe,lt_min hζo hζe,?_⟩
  intro p hp hp1 ρ hρ q
  obtain ⟨No,hNo⟩:=ho p hp hp1 (q+1)
  obtain ⟨Ne,hNe⟩:=he p hp hp1 (q+1)
  obtain ⟨Ns,hNs⟩:=select_mixed_boundary_factors_avoiding ρ hρ
  refine ⟨max 2 (max No (max Ne Ns)),?_⟩
  intro V W J K E _ _ _ _ _ _ _ _ _ _ hn hJ hK Q F P B₀ e hQ T S U f g hSU
    hsize hF hB₀ hcommon hcounts wt we hw hew herr heerr
  have hVW:Fintype.card V≤Fintype.card W:=Fintype.card_le_of_injective e e.injective
  have hnV:0<Fintype.card V:=by omega
  have hnR:(0:ℝ)<Fintype.card V:=Nat.cast_pos.mpr hnV
  have po:=hNo V J E (by omega) hJ Q F T f hsize
    (fun v=>(hF v).trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _)))
    (by simpa only [ite_true] using hcommon) wt hw
    (fun j v hv=>(herr j v hv).trans (min_le_left _ _))
  have pe:=hNe W K E (by omega) hK P B₀ S U g hSU
    (fun w=>(hB₀ w).trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg _)))
    hcounts we hew (fun k w hw=>(heerr k w hw).trans (min_le_right _ _))
  let μ:=FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp.le hp1)
  have combine (Ao Ae:(E→Bool)→Prop)
      (hAo:1-1/(Fintype.card V:ℝ)^(q+1)≤μ.probability Ao)
      (hAe:1-1/(Fintype.card W:ℝ)^(q+1)≤μ.probability Ae):
      1-1/(Fintype.card V:ℝ)^q≤μ.probability (fun σ=>Ao σ∧Ae σ):=by
    have hfrac:1/(Fintype.card W:ℝ)^(q+1)≤1/(Fintype.card V:ℝ)^(q+1):=
      div_le_div_of_nonneg_left (by norm_num) (pow_pos hnR _) (pow_le_pow_left₀ hnR.le (Nat.cast_le.mpr hVW) _)
    have hi:=finiteLaw_good_intersection μ Ao Ae (1/(Fintype.card W:ℝ)^(q+1)) hAe
    have hb':=scaled_inverse_power_le (Fintype.card V) q hnV 2 (by exact_mod_cast (show 2≤Fintype.card V by omega))
    have hb'':2*(1/(Fintype.card V:ℝ)^(q+1))≤1/(Fintype.card V:ℝ)^q:=by convert hb' using 1 <;> ring
    linarith only [hAo,hi,hfrac,hb'']
  have hjoint:=combine _ _ po pe
  apply hjoint.trans
  apply finiteLaw_probability_mono
  intro σ hσ Y Z K₀ δ hK₀ hYT hdiv hZU hratio hchangeY hchangeZ hinter hmem hbudgetY hbudgetZ
  apply hNs V W J K (by omega) 3 Q F P B₀ e hQ T Y S U Z hSU K₀ δ hK₀ hinter hmem
  · intro j H hH
    have hscale:(min ζo ζe)*(p*(T j).card)≤ζo*(p*(T j).card):=
      mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
    obtain ⟨D,hD,_hs,_hd,ha⟩:=hσ.1 j (Y j) (hYT j) (hdiv j)
      ((hchangeY j).trans hscale) H (fun v=>(hH v).trans ((hbudgetY j).trans hscale))
    exact ⟨D,hD,ha⟩
  · intro k H hH
    have hscale:(min ζo ζe)*(p*(U k).card)≤ζe*(p*(U k).card):=
      mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
    exact hσ.2 k (Z k) (hZU k) (hratio k) ((hchangeZ k).trans hscale) H
      (fun w=>(hH w).trans ((hbudgetZ k).trans hscale))

end Oberwolfach
