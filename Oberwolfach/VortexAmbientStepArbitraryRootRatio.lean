module

public import Oberwolfach.VortexSubsetStepArbitraryRootRatio
public import Oberwolfach.AmbientSubset

@[expose] public section
/-! Ambient roots need only be bounded by a fixed multiple of the current
vortex set, so earlier levels can be tested as well. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
universe w

theorem vortex_ambient_subset_step_root_ratio {ε C:ℝ} (he:0<ε) (he1:ε≤1) (hC:0<C):
    ∃N:ℕ,∀(V:Type w) (B R:Finset V) (A:V→Finset V),
      N≤B.card→(R.card:ℝ)≤C*B.card→
      ∃S:Finset V,S⊆B ∧ S.card=Nat.floor (ε*B.card) ∧
        ∀x∈R,|((A x∩S).card:ℝ)/S.card-((A x∩B).card:ℝ)/B.card|<(B.card:ℝ)^(-1/3:ℝ) :=by
  obtain ⟨N,hN⟩:=vortex_uniform_subset_step_root_ratio.{w,w} he he1 hC
  refine ⟨N,?_⟩
  intro V B R A hn hR
  let : DecidableEq {x // x∈B}:=Classical.decEq _
  let A' (x:V):=(A x).subtype (fun y=>y∈B)
  obtain ⟨S,hS⟩:=hN {y // y∈B} (by simpa using hn) V R A' (by simpa using hR)
  let Cset:=S.1.map (Function.Embedding.subtype (fun y=>y∈B))
  have hcard:Cset.card=Nat.floor (ε*B.card):=by
    simpa only [Cset,Finset.card_map,Fintype.card_coe] using S.2
  refine ⟨Cset,subtype_sample_subset B S.1,hcard,?_⟩
  intro x hx
  have hh:=hS x hx
  dsimp only [A'] at hh
  rw [subtype_sample_intersection_card (A x) B S.1,subtype_restriction_card (A x) B] at hh
  simpa only [Fintype.card_coe,←hcard] using hh
end Oberwolfach
