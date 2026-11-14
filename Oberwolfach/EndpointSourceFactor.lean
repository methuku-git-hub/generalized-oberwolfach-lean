module

public import Oberwolfach.EndpointSourceCounts
public import Oberwolfach.EndpointFactorOnDomain

@[expose] public section

/-! The endpoint factor conclusion from the actual source row/index estimates.
The triangle factor is constructed on A union B inside the original ambient graph.
The weights are supplied on genuine unordered triangles; all absorber counts
and the conversion from the original row scale are proved. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 5500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem endpoint_source_factor (p κ b B₀ : ℝ) (hp : 0<p) (hp1 : p≤1) (hκ : 0<κ)
    (hb : 0<b) (hB₀ : 0≤B₀) :
    ∃ ε₀ τ η : ℝ,0<ε₀ ∧ 0<τ ∧ 0<η ∧ ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V],
      ∀ (P R H F : SimpleGraph V) (A B : Finset V) (x : V),N≤A.card →
      B.card≤A.card → Disjoint A B → R≤P\F →
      ∀ q s ε L : ℝ,p≤q → p≤s → ε≤ε₀ → 0≤L → L≤τ*A.card →
      κ*A.card≤(B.card:ℝ) →
      (∀ v∈insert x A,(3/4:ℝ)*A.card≤((A∩P.neighborFinset v).card:ℝ)) →
      (∀ v,(F.degree v:ℝ)≤L) →
      (∀ X J : Finset V,x∈X → X⊆insert x A → J⊆B →
        X.card≤3 → J.card≤2 → X.card+J.card≤4 →
        q^X.card*s^J.card*((common A X (fun v=>(P\F).neighborFinset v)).card:ℝ)-ε*A.card≤
          ((common (common A X (fun v=>R.neighborFinset v)) J (fun v=>H.neighborFinset v)).card:ℝ)) →
      (∀ X : Finset V,x∈X → X⊆insert x A → (X.card=1 ∨ X.card=3) →
        (∀ v∈X,∀ w∈X,¬F.Adj v w) →
        (s^X.card-ε)*B.card≤((common B X (fun v=>H.neighborFinset v)).card:ℝ)) →
      let S := common A {x} (fun v=>R.neighborFinset v)
      let T := common B {x} (fun v=>H.neighborFinset v)
      S.card=2*T.card →
      ∀ wt : EndpointTriangle (endpointHostGraph R H A B) F S T→ℝ,
      (∀ C,b/(A.card:ℝ)^2≤wt C ∧ wt C≤B₀/(A.card:ℝ)^2) →
      (∀ v∈S∪T,|1-hypergraphWeightedDegree endpointTriangleVertices wt v|≤η) →
      HasResourceDecomposition (endpointTriangleVertices (Q:=endpointHostGraph R H A B) (F:=F) (S:=S) (T:=T)) (S∪T) := by
  let γ₀ := endpointCountCoefficient p κ
  have hγ₀ : 0<γ₀ := endpointCountCoefficient_pos p κ hp hκ
  let γ := γ₀/3
  have hγ : 0<γ := by dsimp [γ];positivity
  obtain ⟨εf,η,hεf,hη,N,hfactor⟩ := endpoint_triangle_factor_on_domain γ b (9*B₀) hγ hb (by positivity)
  let ε₀ := min (p^4/16) (p^3/2)
  let τ := min εf (1/24)
  have hε₀ : 0<ε₀ := by dsimp [ε₀];positivity
  have hτ : 0<τ := lt_min hεf (by norm_num)
  refine ⟨ε₀,τ,η,hε₀,hτ,hη,max N 1,?_⟩
  intro V _ _ P R H F A B x hn hBA hAB hR q s ε L hq hs hε hL hLτ hB hdeg hF hrows hindices
  dsimp only
  intro hratio wt hw herr
  let Ω := A∪B
  let S := common A {x} (fun v=>R.neighborFinset v)
  let T := common B {x} (fun v=>H.neighborFinset v)
  let Q := endpointHostGraph R H A B
  have hAn : (A.card:ℝ)≤Ω.card := by exact_mod_cast Finset.card_le_card (show A⊆Ω from Finset.subset_union_left)
  have ha : (0:ℝ)<A.card := by exact_mod_cast (le_max_right N 1).trans hn
  have hnpos : (0:ℝ)<Ω.card := ha.trans_le hAn
  have hΩupper:Ω.card≤3*A.card:=by
    have hh:=Finset.card_union_le A B
    dsimp [Ω];omega
  have hnA' : (Ω.card:ℝ)≤3*A.card := by exact_mod_cast hΩupper
  have hL24 : L≤(A.card:ℝ)/24 := by
    have hh:=mul_le_mul_of_nonneg_right (min_le_right εf (1/24:ℝ)) (Nat.cast_nonneg A.card)
    dsimp [τ] at hLτ;linarith only [hh,hLτ]
  have hc := endpoint_source_counts P R H F A B x hAB hR p q s ε L κ hp hp1 hq hs hκ hB hL hL24 hε hdeg hF hrows hindices
  have hscale : γ*Ω.card≤γ₀*A.card := by dsimp [γ];nlinarith only [mul_le_mul_of_nonneg_left hnA' hγ₀.le]
  have hc' : EndpointNeighbourCounts Q F S T (γ*Ω.card) :=
    ⟨hscale.trans hc.indices,fun Y J hY hJ hYc hJc hYJ=>hscale.trans (hc.rows Y J hY hJ hYc hJc hYJ),
      fun v hv w hw hne hnf=>hscale.trans (hc.pairs v hv w hw hne hnf)⟩
  have hweights (C : EndpointTriangle Q F S T) :
      b/(Ω.card:ℝ)^2≤wt C ∧ wt C≤(9*B₀)/(Ω.card:ℝ)^2 := by
    constructor
    · exact (div_le_div_of_nonneg_left hb.le (pow_pos ha _) (pow_le_pow_left₀ ha.le hAn _)).trans (hw C).1
    · apply (hw C).2.trans
      apply (div_le_div_iff₀ (pow_pos ha _) (pow_pos hnpos _)).mpr
      have hh:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnpos.le hnA' 2) hB₀
      nlinarith only [hh]
  apply hfactor V Q F Ω S T
    (((le_max_left N 1).trans hn).trans (Finset.card_le_card Finset.subset_union_left))
    (fun v hv=>Finset.mem_union_left B (((mem_common_iff _ _ _ _).mp hv).1))
    (fun v hv=>Finset.mem_union_right A (((mem_common_iff _ _ _ _).mp hv).1))
    (hAB.mono (fun v hv=>((mem_common_iff _ _ _ _).mp hv).1) (fun v hv=>((mem_common_iff _ _ _ _).mp hv).1))
    hratio (fun v _=>(hF v).trans (hLτ.trans ((mul_le_mul_of_nonneg_right (min_le_left εf (1/24:ℝ))
      (Nat.cast_nonneg A.card)).trans (mul_le_mul_of_nonneg_left hAn hεf.le)))) hc' wt hweights
  exact herr

end Oberwolfach
