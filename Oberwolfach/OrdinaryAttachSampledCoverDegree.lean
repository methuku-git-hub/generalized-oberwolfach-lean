module

public import Oberwolfach.OrdinarySampledCoverDegree
public import Oberwolfach.FiniteLawAttachConditionalEvent

@[expose] public section
/-! The cover is selected on the earlier outcome, then tested on the same
fresh physical-edge coins used for the rest of the construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_attach_sampled_cover_degree
    (p δ:ℝ) (hp:0≤p) (hp1:p≤1) (hδ:0<δ) (q:ℕ):
    ∃N:ℕ,∀(V U Ω:Type) [Fintype V] [Fintype U] [Fintype Ω] [DecidableEq V] [DecidableEq U],
      N≤Fintype.card (V⊕U)→∀(μ:FiniteLaw Ω) (E:Ω→Prop)
      (B:(Σ _ : Ω, Sym2 (V⊕U)→Bool)→Prop) (loss:ℝ) (cover:Ω→SimpleGraph (V⊕U)),
    let law:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp hp1);
    1-loss≤(μ.sigma (fun _=>law)).probability B→(∀z,B z→E z.1)→
    1-(loss+1/(Fintype.card (V⊕U):ℝ)^q)≤(μ.sigma (fun _=>law)).probability
      (fun z=>B z∧OrdinarySampledCoverDegreeGood (cover z.1) p δ z.2):=by
  obtain ⟨N,hN⟩:=ordinary_sampled_cover_degree_high_probability p δ hp hp1 hδ q
  refine ⟨N,?_⟩
  intro V U Ω _ _ _ _ _ hn μ E B loss cover law hB hBE
  apply finiteLaw_attach_conditional_event μ (fun _=>law) E B
    (fun a σ=>OrdinarySampledCoverDegreeGood (cover a) p δ σ) loss
    (1/(Fintype.card (V⊕U):ℝ)^q) (by positivity) hB hBE
  intro a _
  exact hN V U hn (cover a)
end Oberwolfach
