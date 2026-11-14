module

public import Oberwolfach.FreshBipartiteCommonEvent
public import Oberwolfach.EndpointPairing

@[expose] public section

/-! Actual endpoint assignments on the common sampled event, with the
final two-to-one ratio imposed after sampling and after all allowed changes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem fresh_neighbour_pair_common_event (p₀ a:ℝ)
    (hp₀:0<p₀) (hp₀1:p₀≤1) (ha:0<a) (ha1:a≤1):
    ∃ η ζ:ℝ,0<η ∧ 0<ζ ∧ ∀ (b q:ℕ) (ρ:ℝ) (hρ:0<ρ) (hρ1:ρ≤1),
    ∃ N:ℕ,∀ (V J:Type) [Fintype V] [DecidableEq V] [Fintype J],
      N≤Fintype.card V→Fintype.card J≤(Fintype.card V)^2→
      ∀ (G F:J→SimpleGraph V) (A B:J→Finset V) (p:J→ℝ),
      (∀ j,p₀≤p j ∧ p j≤1)→
      (∀ j,a*Fintype.card V≤((A j).card:ℝ) ∧ a*Fintype.card V≤((B j).card:ℝ))→
      (∀ j,Disjoint (A j) (B j))→
      (∀ j v,(F j).degree v≤b)→
      (∀ j v,v∈A j→|(((B j)∩(G j).neighborFinset v).card:ℝ)-p j*(B j).card|≤η*(B j).card)→
      (∀ j v,v∈B j→|(((A j)∩(G j).neighborFinset v).card:ℝ)-p j*(A j).card|≤η*(A j).card)→
      (∀ j v,v∈A j→∀ w,w∈A j→v≠w→¬(F j).Adj v w→
        ((((B j)∩(G j).neighborFinset v)∩(G j).neighborFinset w).card:ℝ)≤(p j^2+η)*(B j).card)→
      1-1/(Fintype.card V:ℝ)^q≤
        (FiniteLaw.pi (fun _:V=>FiniteLaw.retentionCoin ρ hρ.le hρ1)).probability
        (fun σ=>∀ j (A'' B'':Finset V) (D:SimpleGraph V),A''⊆A j→B''⊆B j→
          ((changed A'' ((A j)∩bernoulliVertexSet σ)).card:ℝ)≤ζ*(ρ*Fintype.card V)→
          ((changed B'' ((B j)∩bernoulliVertexSet σ)).card:ℝ)≤ζ*(ρ*Fintype.card V)→
          (∀ v,(D.degree v:ℝ)≤ζ*(ρ*Fintype.card V))→
          A''.card=2*B''.card→Nonempty (EndpointPairing ((G j)\D) (F j) A'' B''))
:=by
  obtain ⟨η,ζ,hη,hζ,hfresh⟩:=fresh_bipartite_common_event p₀ a (p₀/64) hp₀ hp₀1 ha ha1 (by positivity)
  refine ⟨η,ζ,hη,hζ,?_⟩
  intro b q ρ hρ hρ1
  obtain ⟨N₁,hN₁⟩:=hfresh b q ρ hρ hρ1
  obtain ⟨N₂,hN₂⟩:=endpoint_pairing_of_degree_cuts (p₀/2) (by positivity) b
  obtain ⟨N₃,hN₃⟩:=exists_nat_ge (2*(N₂:ℝ)/(ρ*a))
  refine ⟨max N₁ N₃,?_⟩
  intro V J _ _ _ hn hJ G F A B p hp hsize hdis hF hrow hcol hcodeg
  have hevent:=hN₁ V J (by omega) hJ G F A B p hp hsize hF hrow hcol hcodeg
  apply hevent.trans
  apply finiteLaw_probability_mono
  intro σ hσ j A'' B'' D hAA hBB hca hcb hD hbal
  obtain ⟨hsa,hsb,hdA,hdB,hcut⟩:=hσ j A'' B'' D hAA hBB hca hcb hD
  have horder:N₂≤B''.card:=by
    have hn3:(N₃:ℝ)≤Fintype.card V:=by exact_mod_cast (show N₃≤Fintype.card V by omega)
    have hh:2*(N₂:ℝ)≤(Fintype.card V:ℝ)*(ρ*a):=
      (div_le_iff₀ (mul_pos hρ ha)).mp (hN₃.trans hn3)
    have hs:=mul_le_mul_of_nonneg_left (hsize j).2 hρ.le
    have ht:(N₂:ℝ)≤B''.card:=by nlinarith only [hh,hs,hsb]
    exact_mod_cast ht
  apply hN₂ V ((G j)\D) (F j) A'' B'' horder hbal ((hdis j).mono hAA hBB) (hF j)
    (by intro v hv;convert hdA v hv using 1;congr 2;ext w;simp only [Finset.mem_inter,SimpleGraph.mem_neighborFinset])
    (by intro v hv;convert hdB v hv using 1;congr 2;ext w;simp only [Finset.mem_inter,SimpleGraph.mem_neighborFinset])
  intro S hS T hT hSc hTc
  have hSε:p₀/64*A''.card≤(S.card:ℝ):=by
    rw [hbal,Nat.cast_mul,Nat.cast_ofNat]
    nlinarith only [hSc]
  have hTε:p₀/64*B''.card≤(T.card:ℝ):=by
    have hpos:0≤p₀*(B''.card:ℝ):=by positivity
    nlinarith only [hTc,hpos]
  convert hcut S hS T hT hSε hTε using 1
  congr 2
  funext v w
  by_cases h:((G j)\D).Adj v w <;> simp only [h,ite_true,ite_false]

end Oberwolfach
