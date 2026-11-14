module

public import Oberwolfach.OrdinaryTerminalCandidates
public import Oberwolfach.OrdinaryIndexedTerminalReservoir

@[expose] public section
/-! One reservoir for every bounded admissible terminal remainder on a
fixed terminal row/hub pair, with an ambient-size-independent cost. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_all_terminal_reservoir
    (r m f a b f₀:ℕ) (γ ε:ℝ) (Q F:SimpleGraph V) (H:V→U→Prop)
    (Wterm W:Finset V) (Bterm B:Finset U)
    (hWW:Wterm⊆W) (hBB:Bterm⊆B) (hW:W.card≤f) (hB:(B.card:ℝ)≤γ)
    (L:ℕ) (hL:2^(Wterm.card*Wterm.card+Wterm.card*Bterm.card)≤L)
    (hWbudget:f+L*a≤f₀) (hBbudget:γ+L*b≤ε*Fintype.card V+f₀)
    (hlocal:∀(G:SimpleGraph V) (Hs:V→U→Prop) (W':Finset V) (B':Finset U),
      (ordinaryPhysicalGraph G Hs).support.toFinset.card≤m →
      (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card) →
      (∀u,r∣(Finset.univ.filter (fun v=>Hs v u)).card) →
      G≤Q → (∀v u,Hs v u→H v u) →
      (∀u,(∃v,Hs v u)→u∈B') → W'.card≤f₀ →
      (B'.card:ℝ)≤ε*Fintype.card V+f₀ →
      ∃C:Finset (Sym2 V⊕(V×U)),
        IsResourceAbsorber (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
          (ordinaryHostResources G Hs) C ∧ C⊆ordinaryHostResources Q H ∧
        (ordinaryResourceRows C).card≤a ∧ (ordinaryResourceHubs C).card≤b ∧
        Disjoint C (ordinaryRootResources W' B')):
    ∃C:Finset (Sym2 V⊕(V×U)),C⊆ordinaryHostResources Q H ∧
      Disjoint C (ordinaryRootResources W B) ∧
      (ordinaryResourceRows C).card≤L*a ∧ (ordinaryResourceHubs C).card≤L*b ∧
      HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) C ∧
      ∀(G:SimpleGraph V) (Hs:V→U→Prop),
        ordinaryHostResources G Hs⊆ordinaryRootResources Wterm Bterm →
        (ordinaryPhysicalGraph G Hs).support.toFinset.card≤m →
        (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card) →
        (∀u,r∣(Finset.univ.filter (fun v=>Hs v u)).card) →
        G≤Q → (∀v u,Hs v u→H v u) →
        IsResourceAbsorber (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
          (ordinaryHostResources G Hs) C:=by
  let I:=OrdinaryTerminalCandidate r m Q H Wterm Bterm
  have hcard:Fintype.card I≤L:=(ordinary_terminal_candidate_card_bound r m Q H Wterm Bterm).trans hL
  have hcardR:(Fintype.card I:ℝ)≤L:=by exact_mod_cast hcard
  have hroot:ordinaryRootResources Wterm Bterm⊆ordinaryRootResources W B:=
    ordinaryRootResources_contains _ _ _
      ((ordinaryRootResources_rows Wterm Bterm).trans hWW)
      ((ordinaryRootResources_hubs Wterm Bterm).trans hBB)
  have hchoose:∀(W':Finset V) (B':Finset U),W⊆W'→B⊆B'→
      W'.card≤f+Fintype.card I*a→(B'.card:ℝ)≤γ+Fintype.card I*b→∀i:I,
      ∃C:Finset (Sym2 V⊕(V×U)),
        IsResourceAbsorber (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) i.val C ∧
        C⊆ordinaryHostResources Q H ∧ (ordinaryResourceRows C).card≤a ∧
        (ordinaryResourceHubs C).card≤b ∧ Disjoint C (ordinaryRootResources W' B'):=by
    intro W' B' hWW' hBB' hw hb i
    obtain ⟨hiroot,G,Hs,hEq,hs,hbal,hdiv,hG,hH⟩:=i.property
    have hactive:∀u,(∃v,Hs v u)→u∈B':=by
      intro u ⟨v,hvu⟩
      have he:Sum.inr (v,u)∈i.val:=by rw [hEq];exact (ordinaryHostResources_spoke G Hs v u).mpr hvu
      exact hBB' (hBB ((ordinaryRootResources_spoke_iff Wterm Bterm v u).mp (hiroot he)).2)
    have hw':W'.card≤f₀:=hw.trans (le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right a hcard) f) hWbudget)
    have hb':(B'.card:ℝ)≤ε*Fintype.card V+f₀:=by
      have hmul:(Fintype.card I:ℝ)*b≤(L:ℝ)*b:=mul_le_mul_of_nonneg_right hcardR (by positivity)
      exact hb.trans (by linarith)
    obtain ⟨C,habs,hhost,hr,hu,havoid⟩:=hlocal G Hs W' B' hs hbal hdiv hG hH hactive hw' hb'
    refine ⟨C,?_,hhost,hr,hu,havoid⟩
    simpa only [hEq] using habs
  obtain ⟨C,hhost,havoid,hr,hu,hdec,habs⟩:=ordinary_indexed_terminal_reservoir
    f a b γ W B hW hB (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
    (ordinaryHostResources Q H) (fun i:I=>i.val) (fun i=>i.property.1.trans hroot) hchoose
  refine ⟨C,hhost,havoid,hr.trans (Nat.mul_le_mul_right a hcard),
    hu.trans (Nat.mul_le_mul_right b hcard),hdec,?_⟩
  intro G Hs hrootL hs hbal hdiv hG hH
  exact habs ⟨ordinaryHostResources G Hs,hrootL,G,Hs,rfl,hs,hbal,hdiv,hG,hH⟩
end Oberwolfach
