module

public import Oberwolfach.OrdinarySequentialResourceSelection
public import Oberwolfach.OrdinaryRootResources
public import Oberwolfach.AlternativeAbsorberAssembly

@[expose] public section
/-! A bounded family of alternative ordinary remainders has one fixed
absorbing reservoir. The alternatives may overlap; each local absorber avoids
the entire common root pair as well as all earlier absorber resources. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Ω:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U] [DecidableEq Ω]

theorem ordinary_finite_terminal_reservoir
    (l f a b:ℕ) (γ:ℝ) (W:Finset V) (B:Finset U)
    (hW:W.card≤f) (hB:(B.card:ℝ)≤γ)
    (R:Ω→Finset (Sym2 V⊕(V×U))) (Host:Finset (Sym2 V⊕(V×U)))
    (L:Fin l→Finset (Sym2 V⊕(V×U)))
    (hL:∀i,L i⊆ordinaryRootResources W B)
    (hchoose:∀(W':Finset V) (B':Finset U),W⊆W'→B⊆B'→
      W'.card≤f+l*a→(B'.card:ℝ)≤γ+l*b→∀i:Fin l,
      ∃C:Finset (Sym2 V⊕(V×U)),
        IsResourceAbsorber R (L i) C ∧ C⊆Host ∧
        (ordinaryResourceRows C).card≤a ∧ (ordinaryResourceHubs C).card≤b ∧
        Disjoint C (ordinaryRootResources W' B')):
    ∃C:Finset (Sym2 V⊕(V×U)),C⊆Host ∧ Disjoint C (ordinaryRootResources W B) ∧
      (ordinaryResourceRows C).card≤l*a ∧ (ordinaryResourceHubs C).card≤l*b ∧
      HasResourceDecomposition R C ∧ ∀i,IsResourceAbsorber R (L i) C:=by
  let Good:=fun i C=>IsResourceAbsorber R (L i) C ∧ C⊆Host
  have hlocal:∀(W':Finset V) (B':Finset U) (F:Finset (Sym2 V⊕(V×U))),
      W⊆W'→B⊆B'→W'.card≤f+l*a→(B'.card:ℝ)≤γ+l*b→
      ordinaryResourceRows F⊆W'→ ordinaryResourceHubs F⊆B'→
      ∀i:Fin l,∃C,Good i C∧(ordinaryResourceRows C).card≤a∧
        (ordinaryResourceHubs C).card≤b∧Disjoint C F:=by
    intro W' B' F hWW hBB hw hb hrows hhubs i
    obtain ⟨C,habs,hhost,hr,hu,havoid⟩:=hchoose W' B' hWW hBB hw hb i
    exact ⟨C,⟨habs,hhost⟩,hr,hu,havoid.mono_right (ordinaryRootResources_contains F W' B' hrows hhubs)⟩
  obtain ⟨K,hK,hKK,hRows,hHubs⟩:=ordinary_sequential_resource_selection l f a b γ W B
    (ordinaryRootResources W B) hW hB (ordinaryRootResources_rows W B)
    (ordinaryRootResources_hubs W B) Good hlocal
  have hAlt:∀i j,Disjoint (K i) (L j):=fun i j=>(hK i).2.2.2.mono_right (hL j)
  have hdec:=alternative_absorber_union R L K (fun i=>(hK i).1.1) hKK hAlt
  refine ⟨Finset.univ.biUnion K,?_,?_,hRows,hHubs,hdec.1,hdec.2⟩
  · intro e he
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp he
    exact (hK i).1.2 hi
  · apply Finset.disjoint_left.mpr
    intro e he hroot
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp he
    exact Finset.disjoint_left.mp (hK i).2.2.2 hi hroot
end Oberwolfach
