module

public import Oberwolfach.BernoulliGraphDomainEvent
public import Oberwolfach.FreshBipartiteRestriction

@[expose] public section

/-! Degree and cut bounds on one Bernoulli event for all later changes.
The parent tolerance and deletion allowance precede the exceptional-pair
bound and the sampling probability. The event covers every original root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem fresh_bipartite_common_event (p₀ a ε:ℝ)
    (hp₀:0<p₀) (hp₀1:p₀≤1) (ha:0<a) (ha1:a≤1) (hε:0<ε):
    ∃ η ζ:ℝ,0<η ∧ 0<ζ ∧ ∀ (b q:ℕ) (ρ:ℝ) (hρ:0<ρ) (hρ1:ρ≤1),
    ∃ N:ℕ,∀ (V J:Type) [Fintype V] [DecidableEq V] [Fintype J],
      N≤Fintype.card V→Fintype.card J≤(Fintype.card V)^2→
      ∀ (G F:J→SimpleGraph V) (A B:J→Finset V) (p:J→ℝ),
      (∀ j,p₀≤p j ∧ p j≤1)→
      (∀ j,a*Fintype.card V≤((A j).card:ℝ) ∧ a*Fintype.card V≤((B j).card:ℝ))→
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
          ρ*(A j).card/2≤(A''.card:ℝ) ∧ ρ*(B j).card/2≤(B''.card:ℝ) ∧
          (∀ v∈A'',p₀/2*B''.card≤((B''∩((G j)\D).neighborFinset v).card:ℝ)) ∧
          (∀ v∈B'',p₀/2*A''.card≤((A''∩((G j)\D).neighborFinset v).card:ℝ)) ∧
          (∀ S:Finset V,S⊆A''→∀ T:Finset V,T⊆B''→ε*A''.card≤(S.card:ℝ)→ε*B''.card≤(T.card:ℝ)→
            p₀/2*S.card*T.card≤(bipartiteMatrixCut (fun v w=>if ((G j)\D).Adj v w then 1 else 0) S T:ℝ))):=by
  let ξ:=ε*a/4
  have hξ:0<ξ:=by dsimp [ξ];positivity
  let η:=min (1/8) (min (p₀/48) (p₀^2*ξ/576))
  have hη:0<η:=by dsimp [η];positivity
  have hη1:η≤1/4:=(min_le_left _ _).trans (by norm_num)
  have hdeg:12*η≤p₀/2:=by
    have hh:η≤p₀/48:=(min_le_right _ _).trans (min_le_left _ _)
    nlinarith
  have hsmall:12*η≤p₀^2*ξ/24:=by
    have hh:η≤p₀^2*ξ/576:=(min_le_right _ _).trans (min_le_right _ _)
    have hn:0≤p₀^2*ξ:=by positivity
    nlinarith only [hh,hn]
  refine ⟨η,η*a,hη,mul_pos hη ha,?_⟩
  intro b q ρ hρ hρ1
  obtain ⟨N₁,hN₁⟩:=bernoulli_graph_domain_common_event (η*ρ*a) (by positivity) q
  let c:=p₀^2*ξ^2*ρ*a/16
  have hc:0<c:=by dsimp [c];positivity
  obtain ⟨N₂,hN₂⟩:=exists_nat_ge ((b+1:ℝ)/c)
  refine ⟨max N₁ (max N₂ 1),?_⟩
  intro V J _ _ _ hn hJ G F A B p hp hsize hF hrow hcol hcodeg
  have hn0:0<Fintype.card V:=by omega
  have hnR:0<(Fintype.card V:ℝ):=by exact_mod_cast hn0
  have hlarge₀:(b+1:ℝ)≤c*Fintype.card V:=by
    have hN₂':(N₂:ℝ)≤Fintype.card V:=by exact_mod_cast (show N₂≤Fintype.card V by omega)
    have hh:((b+1:ℝ)/c)≤Fintype.card V:=hN₂.trans hN₂'
    have hh':(b+1:ℝ)≤(Fintype.card V:ℝ)*c:=(div_le_iff₀ hc).mp hh
    simpa only [mul_comm] using hh'
  have hevent:=hN₁ V J (by omega) hJ G A B ρ hρ.le hρ1
  apply hevent.trans
  apply finiteLaw_probability_mono
  intro σ hσ j A'' B'' D hAA hBB hchangeA hchangeB hD
  have hpj:0<p j:=hp₀.trans_le (hp j).1
  have hp2:p₀^2≤p j^2:=by nlinarith [(hp j).1]
  have hscale (C:Finset V) (hC:a*Fintype.card V≤(C.card:ℝ)):
      η*ρ*a*Fintype.card V≤η*(ρ*C.card):=by
    have hh:=mul_le_mul_of_nonneg_left hC (show 0≤η*ρ by positivity)
    nlinarith only [hh]
  have hsa:=hscale (A j) (hsize j).1
  have hsb:=hscale (B j) (hsize j).2
  have hca:((changed A'' ((A j)∩bernoulliVertexSet σ)).card:ℝ)≤η*(ρ*(A j).card):=by
    nlinarith only [hchangeA,hsa]
  have hcb:((changed B'' ((B j)∩bernoulliVertexSet σ)).card:ℝ)≤η*(ρ*(B j).card):=by
    nlinarith only [hchangeB,hsb]
  have hda:∀ v,(D.degree v:ℝ)≤η*(ρ*(A j).card):=by
    intro v;nlinarith only [hD v,hsa]
  have hdb:∀ v,(D.degree v:ℝ)≤η*(ρ*(B j).card):=by
    intro v;nlinarith only [hD v,hsb]
  have hszA:|(((A j)∩bernoulliVertexSet σ).card:ℝ)-ρ*(A j).card|≤η*(ρ*(A j).card):=
    (hσ j).1.le.trans hsa
  have hszB:|(((B j)∩bernoulliVertexSet σ).card:ℝ)-ρ*(B j).card|≤η*(ρ*(B j).card):=
    (hσ j).2.1.le.trans hsb
  have hsrow:∀ v∈A j,|((((B j)∩bernoulliVertexSet σ)∩(G j).neighborFinset v).card:ℝ)-
      ρ*((B j)∩(G j).neighborFinset v).card|≤η*(ρ*(B j).card):=by
    intro v hv
    simpa only [Finset.inter_right_comm] using ((hσ j).2.2.2.1 v).le.trans hsb
  have hscol:∀ v∈B j,|((((A j)∩bernoulliVertexSet σ)∩(G j).neighborFinset v).card:ℝ)-
      ρ*((A j)∩(G j).neighborFinset v).card|≤η*(ρ*(A j).card):=by
    intro v hv
    simpa only [Finset.inter_right_comm] using ((hσ j).2.2.1 v).le.trans hsa
  have hscod:∀ v∈A j,∀ w∈A j,v≠w→¬(F j).Adj v w→
      |(((((B j)∩bernoulliVertexSet σ)∩(G j).neighborFinset v)∩(G j).neighborFinset w).card:ℝ)-
        ρ*(((B j)∩(G j).neighborFinset v)∩(G j).neighborFinset w).card|≤η*(ρ*(B j).card):=by
    intro v hv w hw hne hfw
    simpa only [Finset.inter_assoc,Finset.inter_left_comm,Finset.inter_comm] using
      ((hσ j).2.2.2.2 v w).le.trans hsb
  have hBj:0<(B j).card:=by
    have hh:(0:ℝ)<(B j).card:=(mul_pos ha hnR).trans_le (hsize j).2
    exact_mod_cast hh
  have hlarge:(b+1:ℝ)≤p j^2*ξ^2*(ρ*(B j).card)/16:=by
    have h1:=mul_le_mul_of_nonneg_left (hsize j).2 (show 0≤p₀^2*ξ^2*ρ/16 by positivity)
    have h2:=mul_le_mul_of_nonneg_right hp2 (show 0≤ξ^2*(ρ*(B j).card)/16 by positivity)
    dsimp [c] at hlarge₀
    nlinarith only [hlarge₀,h1,h2]
  have hsm:12*η≤p j^2*ξ/24:=by
    have hh:=mul_le_mul_of_nonneg_right hp2 (show 0≤ξ/24 by positivity)
    nlinarith only [hsmall,hh]
  have hdp:12*η≤p j/2:=by linarith [(hp j).1]
  have hr:=fresh_bipartite_restriction (G j) (F j) D (A j) (B j)
    ((A j)∩bernoulliVertexSet σ) ((B j)∩bernoulliVertexSet σ) A'' B''
    (p j) ρ η ξ b hpj (hp j).2 hρ hη.le hη1 hξ hBj hAA hBB (hF j)
    (hrow j) (hcol j) (hcodeg j) hszA hszB hsrow hscol hscod hca hcb hda hdb hdp hsm hlarge
  have hszA':=sampled_domain_size_after_changes (A j) ((A j)∩bernoulliVertexSet σ) A''
    ρ η hρ.le hη.le hη1 hszA hca
  have hszB':=sampled_domain_size_after_changes (B j) ((B j)∩bernoulliVertexSet σ) B''
    ρ η hρ.le hη.le hη1 hszB hcb
  have hratio:a/4*(B''.card:ℝ)≤A''.card:=by
    have hBcard:((B j).card:ℝ)≤Fintype.card V:=by exact_mod_cast Finset.card_le_univ (B j)
    have hbup:=mul_le_mul_of_nonneg_left hBcard (show 0≤2*ρ by positivity)
    have haup:=mul_le_mul_of_nonneg_left (hsize j).1 (show 0≤ρ/2 by positivity)
    have hh:=mul_le_mul_of_nonneg_left hszB'.2.2 (show 0≤a/4 by positivity)
    have hbup':=mul_le_mul_of_nonneg_left hbup (show 0≤a/4 by positivity)
    nlinarith only [hszA'.2.1,haup,hh,hbup']
  refine ⟨hszA'.2.1,hszB'.2.1,?_,?_,?_⟩
  · intro v hv
    have hh:=mul_le_mul_of_nonneg_right (hp j).1 (show 0≤(B''.card:ℝ)/2 by positivity)
    nlinarith only [hr.1 v hv,hh]
  · intro v hv
    have hh:=mul_le_mul_of_nonneg_right (hp j).1 (show 0≤(A''.card:ℝ)/2 by positivity)
    nlinarith only [hr.2.1 v hv,hh]
  · intro S hS T hT hSc hTc
    have hSξ:ξ*B''.card≤(S.card:ℝ):=by
      have hh:=mul_le_mul_of_nonneg_left hratio hε.le
      dsimp [ξ];nlinarith only [hh,hSc]
    have hTξ:ξ*B''.card≤(T.card:ℝ):=by
      have hh:=mul_le_mul_of_nonneg_left ha1 (show 0≤ε*(B''.card:ℝ)/4 by positivity)
      have hnn:0≤ε*(B''.card:ℝ):=by positivity
      dsimp [ξ];nlinarith only [hh,hnn,hTc]
    have hh:=hr.2.2 S hS T hT hSξ hTξ
    have hpbound:=mul_le_mul_of_nonneg_right (hp j).1 (show 0≤(S.card:ℝ)*T.card/2 by positivity)
    nlinarith only [hh,hpbound]

end Oberwolfach
