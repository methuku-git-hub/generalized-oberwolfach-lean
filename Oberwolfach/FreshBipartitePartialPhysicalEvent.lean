module

public import Oberwolfach.PartialPhysicalSampling
public import Oberwolfach.FixedDomainQuadraticEvent
public import Oberwolfach.FiniteProductProjection

@[expose] public section

/-! Degree and cut bounds in the original physical-edge experiment.
Each fixed root has an injective vertex-to-coordinate map; events for
different roots may overlap. One event covers all subsequent deletions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem fresh_bipartite_partial_physical_event (p₀ a ε:ℝ)
    (hp₀:0<p₀) (hp₀1:p₀≤1) (ha:0<a) (ha1:a≤1) (hε:0<ε):
    ∃ η ζ:ℝ,0<η ∧ 0<ζ ∧ ∀ (b q:ℕ) (ρ:ℝ) (hρ:0<ρ) (hρ1:ρ≤1),
    ∃ N:ℕ,∀ (V J E:Type) [Fintype V] [DecidableEq V] [Fintype J] [Fintype E] [DecidableEq E],
      N≤Fintype.card V→Fintype.card J≤(Fintype.card V)^2→
      ∀ (G F:J→SimpleGraph V) (A B:J→Finset V) (p:J→ℝ) (f:J→V→E),
      (∀ j,Set.InjOn (f j) ((A j∪B j):Set V))→
      (∀ j,p₀≤p j ∧ p j≤1)→
      (∀ j,a*Fintype.card V≤((A j).card:ℝ) ∧ a*Fintype.card V≤((B j).card:ℝ))→
      (∀ j v,(F j).degree v≤b)→
      (∀ j v,v∈A j→|(((B j)∩(G j).neighborFinset v).card:ℝ)-p j*(B j).card|≤η*(B j).card)→
      (∀ j v,v∈B j→|(((A j)∩(G j).neighborFinset v).card:ℝ)-p j*(A j).card|≤η*(A j).card)→
      (∀ j v,v∈A j→∀ w,w∈A j→v≠w→¬(F j).Adj v w→
        ((((B j)∩(G j).neighborFinset v)∩(G j).neighborFinset w).card:ℝ)≤(p j^2+η)*(B j).card)→
      1-1/(Fintype.card V:ℝ)^q≤
        (FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin ρ hρ.le hρ1)).probability
        (fun σ=>∀ j (A'' B'':Finset V) (D:SimpleGraph V),A''⊆A j→B''⊆B j→
          ((changed A'' ((A j).filter (fun v=>σ (f j v)=true))).card:ℝ)≤ζ*(ρ*Fintype.card V)→
          ((changed B'' ((B j).filter (fun v=>σ (f j v)=true))).card:ℝ)≤ζ*(ρ*Fintype.card V)→
          (∀ v,(D.degree v:ℝ)≤ζ*(ρ*Fintype.card V))→
          ρ*(A j).card/2≤(A''.card:ℝ) ∧ ρ*(B j).card/2≤(B''.card:ℝ) ∧
          (∀ v∈A'',p₀/2*B''.card≤((B''∩((G j)\D).neighborFinset v).card:ℝ)) ∧
          (∀ v∈B'',p₀/2*A''.card≤((A''∩((G j)\D).neighborFinset v).card:ℝ)) ∧
          (∀ S:Finset V,S⊆A''→∀ T:Finset V,T⊆B''→ε*A''.card≤(S.card:ℝ)→ε*B''.card≤(T.card:ℝ)→
            p₀/2*S.card*T.card≤(bipartiteMatrixCut (fun v w=>if ((G j)\D).Adj v w then 1 else 0) S T:ℝ))
):=by
  obtain ⟨η,ζ,hη,hζ,hbase⟩:=fresh_bipartite_physical_event p₀ a ε hp₀ hp₀1 ha ha1 hε
  refine ⟨η,ζ,hη,hζ,?_⟩
  intro b q ρ hρ hρ1
  obtain ⟨N,hN⟩:=hbase b q ρ hρ hρ1
  refine ⟨N,?_⟩
  intro V J E _ _ _ _ _ hn hJ G F A B p f hf hp hsize hF hrow hcol hcodeg
  let f' (j:J):V↪E⊕V:=partialPhysicalEmbedding (A j∪B j) (f j) (by simpa only [Finset.coe_union] using hf j)
  have hh:=hN V J (E⊕V) hn hJ G F A B p f' hp hsize hF hrow hcol hcodeg
  rw [←finiteLaw_pi_injective_projection_event
    (fun _:E⊕V=>FiniteLaw.retentionCoin ρ hρ.le hρ1) (Sum.inl:E→E⊕V) Sum.inl_injective]
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ j A'' B'' D hAA hBB hca hcb hd
  apply hσ j A'' B'' D hAA hBB _ _ hd
  · simpa only [f',partial_physical_filter (A j∪B j) (A j) Finset.subset_union_left] using hca
  · simpa only [f',partial_physical_filter (A j∪B j) (B j) Finset.subset_union_right] using hcb

end Oberwolfach
