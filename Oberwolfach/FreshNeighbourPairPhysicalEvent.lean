module

public import Oberwolfach.FreshNeighbourPairEvent
public import Oberwolfach.EndpointPairingGraph
public import Oberwolfach.FixedDomainQuadraticEvent
public import Oberwolfach.FiniteProductProjection

@[expose] public section

/-! Endpoint assignments in the original physical-edge experiment.
Each fixed root has an injective vertex-to-coordinate map; events for
different roots may overlap. One event covers all subsequent deletions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem fresh_neighbour_pair_physical_event (p₀ a:ℝ)
    (hp₀:0<p₀) (hp₀1:p₀≤1) (ha:0<a) (ha1:a≤1):
    ∃ η ζ:ℝ,0<η ∧ 0<ζ ∧ ∀ (b q:ℕ) (ρ:ℝ) (hρ:0<ρ) (hρ1:ρ≤1),
    ∃ N:ℕ,∀ (V J E:Type) [Fintype V] [DecidableEq V] [Fintype J] [Fintype E] [DecidableEq E],
      N≤Fintype.card V→Fintype.card J≤(Fintype.card V)^2→
      ∀ (G F:J→SimpleGraph V) (A B:J→Finset V) (p:J→ℝ) (f:J→V↪E),
      (∀ j,p₀≤p j ∧ p j≤1)→
      (∀ j,a*Fintype.card V≤((A j).card:ℝ) ∧ a*Fintype.card V≤((B j).card:ℝ))→
      (∀ j,Disjoint (A j) (B j))→
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
          A''.card=2*B''.card→∃ P:EndpointPairing (G j) (F j) A'' B'',Disjoint P.graph D)
:=by
  obtain ⟨η,ζ,hη,hζ,hbase⟩:=fresh_neighbour_pair_common_event p₀ a hp₀ hp₀1 ha ha1
  refine ⟨η,ζ,hη,hζ,?_⟩
  intro b q ρ hρ hρ1
  obtain ⟨Nf,hNf⟩:=hbase b (q+3) ρ hρ hρ1
  obtain ⟨Nc,hNc⟩:=fixed_domain_quadratic_common_event 1 (by norm_num) q
  refine ⟨max Nf (max Nc 1),?_⟩
  intro V J E _ _ _ _ _ hn hJ G F A B p f hp hsize hdis hF hrow hcol hcodeg
  have hn0:0<Fintype.card V:=by omega
  let μ:=FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin ρ hρ.le hρ1)
  let Good:J→(E→Bool)→Prop:=fun j σ=>∀ (A'' B'':Finset V) (D:SimpleGraph V),
    A''⊆A j→B''⊆B j→
    ((changed A'' ((A j).filter (fun v=>σ (f j v)=true))).card:ℝ)≤ζ*(ρ*Fintype.card V)→
    ((changed B'' ((B j).filter (fun v=>σ (f j v)=true))).card:ℝ)≤ζ*(ρ*Fintype.card V)→
    (∀ v,(D.degree v:ℝ)≤ζ*(ρ*Fintype.card V))→A''.card=2*B''.card→
    Nonempty (EndpointPairing ((G j)\D) (F j) A'' B'')
  have hgood (j:J):1-1/(Fintype.card V:ℝ)^(q+3)≤μ.probability (Good j):=by
    have hh:=hNf V Unit (by omega) (by simp only [Fintype.card_unit];nlinarith)
      (fun _=>G j) (fun _=>F j) (fun _=>A j) (fun _=>B j) (fun _=>p j)
      (fun _=>hp j) (fun _=>hsize j) (fun _=>hdis j) (fun _=>hF j)
      (fun _=>hrow j) (fun _=>hcol j) (fun _=>hcodeg j)
    rw [←finiteLaw_pi_injective_projection_event
      (fun _:E=>FiniteLaw.retentionCoin ρ hρ.le hρ1) (f j) (f j).injective] at hh
    apply hh.trans
    apply finiteLaw_probability_mono
    intro σ hσ A'' B'' D hAA hBB hca hcb hd hbal
    have he (C:Finset V):C∩bernoulliVertexSet (fun v=>σ (f j v))=
        C.filter (fun v=>σ (f j v)=true):=by
      ext v;simp [bernoulliVertexSet]
    apply hσ () A'' B'' D hAA hBB _ _ hd hbal
    · simpa only [he] using hca
    · simpa only [he] using hcb
  have hevent:=hNc (Fintype.card V) (by omega) (E→Bool) J hJ μ
    (fun _=>Fintype.card V) Good (by intro j;simp) hgood
  apply hevent.trans
  apply finiteLaw_probability_mono
  intro σ hσ j A'' B'' D hAA hBB hca hcb hd hbal
  exact EndpointPairing.deleted_graph_choice (G j) D (F j) A'' B''
    (hσ j A'' B'' D hAA hBB hca hcb hd hbal)

end Oberwolfach
