module

public import Oberwolfach.MixedBoundarySelectionAvoidance
public import Oberwolfach.GreedyGraphCandidates
public import Oberwolfach.OrdinaryFreshDomainsQuadraticEvent
public import Oberwolfach.FreshNeighbourPairPhysicalEvent
public import Oberwolfach.GoodPlacementEvents

@[expose] public section

/-! Joint physical selection after an arbitrary later degree-bounded deletion.
The initial physical sampling law and the original candidate cycles remain
fixed. The full realised deletion degree is charged before selecting factors. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 6500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem mixed_fresh_boundary_pairings_avoiding (m:ℕ) (hm:3≤m) (γ κ b B p₀ a:ℝ)
    (hγ:0<γ) (hκ:0<κ) (hb:0<b) (hB:0≤B) (hp₀:0<p₀) (hp₀1:p₀≤1) (ha:0<a) (ha1:a≤1):
    ∃ ε η ζ:ℝ,0<ε ∧ 0<η ∧ 0<ζ ∧
    ∀ (b₀:ℕ) (p:ℝ) (hp:0<p) (hp1:p≤1) (ρ:ℝ) (hρ:0<ρ) (q:ℕ),∃ N:ℕ,
    ∀ (V W J K E:Type) [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
      [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K] [Fintype E] [DecidableEq E],
      N≤Fintype.card V→Fintype.card J≤(Fintype.card V)^2→Fintype.card K≤(Fintype.card W)^2→
    ∀ (Q F:SimpleGraph V) (P B₀:SimpleGraph W) (e:V↪W),Q.map e≤P→
    ∀ (T:J→Finset V) (S U:K→Finset W) (f:J→V↪E) (g:K→W↪E) (t:K→ℝ),
      (∀ k,Disjoint (S k) (U k))→
      (∀ j,κ*Fintype.card V≤((T j).card:ℝ))→
      (∀ k,a*Fintype.card W≤((S k).card:ℝ) ∧ a*Fintype.card W≤((U k).card:ℝ))→
      (∀ k,p₀≤t k ∧ t k≤1)→
      (∀ v,(F.degree v:ℝ)≤ε*Fintype.card V)→
      (∀ w,B₀.degree w≤b₀)→
      (∀ j,∀ X:Finset V,X.card≤2→
        γ*Fintype.card V≤((common (T j) X (fun x=>Q.neighborFinset x)).card:ℝ))→
      (∀ k v,v∈S k→|(((U k)∩P.neighborFinset v).card:ℝ)-t k*(U k).card|≤η*(U k).card)→
      (∀ k v,v∈U k→|(((S k)∩P.neighborFinset v).card:ℝ)-t k*(S k).card|≤η*(S k).card)→
      (∀ k v,v∈S k→∀ w,w∈S k→v≠w→¬B₀.Adj v w→
        ((((U k)∩P.neighborFinset v)∩P.neighborFinset w).card:ℝ)≤(t k^2+η)*(U k).card)→
    ∀ wt:∀ j,LocalOrdinaryCycle Q F (T j) (m+1)→ℝ,
      (∀ j C,b/(Fintype.card V:ℝ)^m≤wt j C ∧ wt j C≤B/(Fintype.card V:ℝ)^m)→
      (∀ j,∀ v∈T j,|1-hypergraphWeightedDegree localOrdinaryVertices (wt j) v|≤η)→
    1-1/(Fintype.card V:ℝ)^q≤
      (FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp.le hp1)).probability
      (fun σ=>∀ (Z:SimpleGraph W) (ℓ:ℝ),(∀ w,(Z.degree w:ℝ)≤ℓ)→∀ (Y:J→Finset V) (S' U':K→Finset W),
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
          ∀ w,((⨆ i,G i).degree w:ℝ)≤2*(ρ*Fintype.card W)):=by
  obtain ⟨εo,ηo,ζo,hεo,hηo,hζo,ho⟩:=ordinary_fresh_domains_quadratic_event m (by omega) γ κ b B hγ hκ hb hB
  obtain ⟨ηe,ζe,hηe,hζe,he⟩:=fresh_neighbour_pair_physical_event p₀ a hp₀ hp₀1 ha ha1
  refine ⟨εo,min ηo ηe,min ζo ζe,hεo,lt_min hηo hηe,lt_min hζo hζe,?_⟩
  intro b₀ p hp hp1 ρ hρ q
  obtain ⟨No,hNo⟩:=ho p hp hp1 (q+1)
  obtain ⟨Ne,hNe⟩:=he b₀ (q+1) p hp hp1
  obtain ⟨Ns,hNs⟩:=select_mixed_boundary_pairings_avoiding ρ hρ
  refine ⟨max 2 (max No (max Ne Ns)),?_⟩
  intro V W J K E _ _ _ _ _ _ _ _ _ _ hn hJ hK Q F P B₀ e hQ T S U f g t hSU
    hsize hsizeE ht hF hB₀ hcommon hrow hcol hcodeg wt hw herr
  have hVW:Fintype.card V≤Fintype.card W:=Fintype.card_le_of_injective e e.injective
  have hnV:0<Fintype.card V:=by omega
  have hnR:(0:ℝ)<Fintype.card V:=Nat.cast_pos.mpr hnV
  have po:=hNo V J E (by omega) hJ Q F T f hsize hF
    (by simpa only [show ¬m=2 by omega,ite_false] using hcommon) wt hw
    (fun j v hv=>(herr j v hv).trans (min_le_left _ _))
  have pe:=hNe W K E (by omega) hK (fun _=>P) (fun _=>B₀) S U t g ht hsizeE hSU
    (fun _=>hB₀)
    (fun k v hv=>(hrow k v hv).trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg _)))
    (fun k v hv=>(hcol k v hv).trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg _)))
    (fun k v hv w hw hne hfw=>(hcodeg k v hv w hw hne hfw).trans
      (mul_le_mul_of_nonneg_right (by linarith [min_le_right ηo ηe] : t k^2+min ηo ηe≤t k^2+ηe) (Nat.cast_nonneg _)))
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
  intro σ hσ Z ℓ hZ Y S' U' hYT hdiv hS hU hratio hchangeY hchangeS hchangeU hinter hmem hbudgetY hbudgetE
  apply hNs V W J K (by omega) (m+1) Q F P B₀ Z e hQ T Y S' U' hinter hmem
  · intro j H hH
    have hscale:(min ζo ζe)*(p*(T j).card)≤ζo*(p*(T j).card):=
      mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
    have hd (v:V):((H⊔Z.comap e).degree v:ℝ)≤ζo*(p*(T j).card):=by
      have hsum:((H⊔Z.comap e).degree v:ℝ)≤(H.degree v:ℝ)+(Z.comap e).degree v:=by
        exact_mod_cast graph_degree_sup_le H (Z.comap e) v
      have hzc:((Z.comap e).degree v:ℝ)≤ℓ:=
        (Nat.cast_le.mpr (graph_comap_degree_le Z e v)).trans (hZ (e v))
      exact hsum.trans ((add_le_add (hH v) hzc).trans ((hbudgetY j).trans hscale))
    obtain ⟨D,hD,_hs,_hd,ha⟩:=hσ.1 j (Y j) (hYT j) (hdiv j)
      ((hchangeY j).trans hscale) (H⊔Z.comap e) (by intro v;simpa only [←SimpleGraph.ncard_neighborSet] using hd v)
    exact ⟨D,hD,ha.mono_right le_sup_left,
      graph_map_disjoint_of_comap _ Z e (ha.mono_right le_sup_right)⟩
  · intro k H hH
    have hscale:(min ζo ζe)*(p*Fintype.card W)≤ζe*(p*Fintype.card W):=
      mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
    have hd (w:W):((H⊔Z).degree w:ℝ)≤ζe*(p*Fintype.card W):=by
      have hsum:((H⊔Z).degree w:ℝ)≤(H.degree w:ℝ)+Z.degree w:=by
        exact_mod_cast graph_degree_sup_le H Z w
      exact hsum.trans ((add_le_add (hH w) (hZ w)).trans (hbudgetE.trans hscale))
    obtain ⟨E,hE⟩:=hσ.2 k (S' k) (U' k) (H⊔Z) (hS k) (hU k)
      ((hchangeS k).trans hscale) ((hchangeU k).trans hscale) (by intro w;simpa only [←SimpleGraph.ncard_neighborSet] using hd w) (hratio k)
    exact ⟨E,hE.mono_right le_sup_left,hE.mono_right le_sup_right⟩

end Oberwolfach
