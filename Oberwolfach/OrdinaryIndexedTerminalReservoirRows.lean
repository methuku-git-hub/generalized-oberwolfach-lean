module

public import Oberwolfach.OrdinaryFiniteTerminalReservoirRows

@[expose] public section
/-! The alternatives may be indexed by any finite type. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Ω I:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  [DecidableEq Ω] [Fintype I]

theorem ordinary_indexed_terminal_reservoir_rows
    (f a b:ℕ) (γ:ℝ) (W T:Finset V) (B:Finset U)
    (hW:W.card≤f) (hB:(B.card:ℝ)≤γ)
    (R:Ω→Finset (Sym2 V⊕(V×U))) (Host:Finset (Sym2 V⊕(V×U)))
    (L:I→Finset (Sym2 V⊕(V×U))) (hL:∀i,L i⊆ordinaryRootResources W B)
    (hchoose:∀(W':Finset V) (B':Finset U),W⊆W'→B⊆B'→
      W'.card≤f+Fintype.card I*a→(B'.card:ℝ)≤γ+Fintype.card I*b→∀i:I,
      ∃C:Finset (Sym2 V⊕(V×U)),
        IsResourceAbsorber R (L i) C ∧ C⊆Host ∧
        (ordinaryResourceRows C).card≤a ∧ (ordinaryResourceHubs C).card≤b ∧
        ordinaryResourceRows C⊆T ∧ Disjoint C (ordinaryRootResources W' B')):
    ∃C:Finset (Sym2 V⊕(V×U)),C⊆Host ∧ Disjoint C (ordinaryRootResources W B) ∧
      (ordinaryResourceRows C).card≤Fintype.card I*a ∧
      (ordinaryResourceHubs C).card≤Fintype.card I*b ∧
      ordinaryResourceRows C⊆T ∧ HasResourceDecomposition R C ∧ ∀i,IsResourceAbsorber R (L i) C:=by
  let e:I≃Fin (Fintype.card I):=Fintype.equivFin I
  obtain ⟨C,hhost,havoid,hrows,hhubs,hdomain,hdec,habs⟩:=
    ordinary_finite_terminal_reservoir_rows (Fintype.card I) f a b γ W T B hW hB R Host
      (fun i=>L (e.symm i)) (fun i=>hL (e.symm i))
      (fun W' B' hWW hBB hw hb i=>hchoose W' B' hWW hBB hw hb (e.symm i))
  refine ⟨C,hhost,havoid,hrows,hhubs,hdomain,hdec,?_⟩
  intro i
  simpa only [Equiv.symm_apply_apply] using habs (e i)
end Oberwolfach
