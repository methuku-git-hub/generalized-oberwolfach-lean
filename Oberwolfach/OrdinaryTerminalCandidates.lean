module

public import Oberwolfach.OrdinaryRootResourceCardinality
public import Oberwolfach.OrdinaryTriangleAbsorberHighProbability

@[expose] public section
/-! Enumerate all bounded, balanced, wheel-divisible terminal resource
sets on a fixed terminal row/hub pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def OrdinaryTerminalCandidate (r m:ℕ) (Q:SimpleGraph V) (H:V→U→Prop)
    (W:Finset V) (B:Finset U) :=
  {L:Finset (Sym2 V⊕(V×U)) // L⊆ordinaryRootResources W B ∧
    ∃(G:SimpleGraph V) (Hs:V→U→Prop), L=ordinaryHostResources G Hs ∧
      (ordinaryPhysicalGraph G Hs).support.toFinset.card≤m ∧
      (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card) ∧
      (∀u,r∣(Finset.univ.filter (fun v=>Hs v u)).card) ∧
      G≤Q ∧ (∀v u,Hs v u→H v u)}

noncomputable instance ordinaryTerminalCandidateFintype (r m:ℕ) (Q:SimpleGraph V)
    (H:V→U→Prop) (W:Finset V) (B:Finset U):
    Fintype (OrdinaryTerminalCandidate r m Q H W B):=by
  unfold OrdinaryTerminalCandidate
  infer_instance

theorem ordinary_terminal_candidate_card_bound (r m:ℕ) (Q:SimpleGraph V)
    (H:V→U→Prop) (W:Finset V) (B:Finset U):
    Fintype.card (OrdinaryTerminalCandidate r m Q H W B)≤
      2^(W.card*W.card+W.card*B.card):=by
  let Root:=ordinaryRootResources W B
  let e:OrdinaryTerminalCandidate r m Q H W B→↥(Root.powerset):=
    fun x=>⟨x.1,Finset.mem_powerset.mpr x.2.1⟩
  have he:Function.Injective e:=by
    intro x y h
    apply Subtype.ext
    have hh:=congrArg (fun z:↥(Root.powerset)=>z.val) h
    exact hh
  have hc:=Fintype.card_le_of_injective e he
  rw [Fintype.card_coe,Finset.card_powerset] at hc
  exact hc.trans (Nat.pow_le_pow_right (by norm_num) (ordinary_root_resources_card_le W B))
end Oberwolfach
