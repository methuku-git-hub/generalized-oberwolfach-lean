module

public import Oberwolfach.MarkedRelativeActiveHostAbsorber
public import Oberwolfach.MarkedFiniteForbiddenResources

@[expose] public section

/-! The marked relative absorber also avoids an arbitrary bounded set of
physical resources. The size of the absorber still precedes that bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 50000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_relative_active_host_absorber_avoiding (l:ℕ) (hl:2≤l)
    (ρ σ q₀ β blo bhi:ℝ) (hρ:0<ρ) (hσ:0<σ) (hq₀:0<q₀) (hβ:0<β) (hblo:0<blo) (hbhi:0<bhi):
    ∃ ε:ℝ,0<ε∧∀ s:ℕ,∃ a₀ b₀:ℕ,∀ f b:ℕ,∀ dF:ℝ,0≤dF→∃ N:ℕ,
    ∀ (V₀ U₀ V U E K A S:Type) [Fintype V₀] [Fintype U₀] [Fintype V] [Fintype U] [Fintype A] [Fintype S]
      [DecidableEq V₀] [DecidableEq U₀] [DecidableEq V] [DecidableEq U] [DecidableEq A] [DecidableEq S],
    N≤Fintype.card V→
    ∀ (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (π:Equiv.Perm V),1≤b→
    ∀ (G:IndexedMarkedGraph V₀ U₀ A S),G.IsBalanced (l+4)→
    G.activeRows.card+G.activeHubs.card≤s→
    ∀ (R:IndexedMarkedHostRealization G tail head ktail khead H₀ HK π b) (W:Finset V) (B:Finset U) (F₀:Finset (Finset V⊕(V×U))),
    F₀.card≤f→(∀ e:Finset V,Sum.inl e∈F₀→e.card≤2)→
    (∀ u,R.active.hubs u∈B)→
    MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l (ρ*Fintype.card V) (σ*Fintype.card V)→
    Function.Injective (markedPhysicalEdge tail head ktail khead π)→
    (B.card:ℝ)≤ε*Fintype.card V+f→(W.card:ℝ)≤ε*Fintype.card V+f→
    ∀ F:SimpleGraph V,permutationConflictGraph π b≤F→
    (∀ v z,HK v z→¬H₀ v z)→(∀ v,(F.degree v:ℝ)≤dF)→
    MarkedCommonPairCycleProfiles tail head ktail khead H₀ HK π b l q₀ β blo bhi ε→
    ∃ C:MarkedSupportedEdgeSet tail head ktail khead π U,
      IsResourceAbsorber (fun D:MarkedWheel tail head ktail khead (l+4) π b H₀ HK=>markedWheelPhysicalResources D)
        R.active.resources C.edges∧Disjoint C.edges F₀∧C.rows.card≤a₀∧C.hubs.card≤b₀∧
      (∀ v∈C.rows,v∈W∪R.active.rowSet→v∈R.active.rowSet)∧(∀ u∈C.hubs,u∈B→u∈R.active.hubSet)∧
      (∀ e∈C.edges,¬MarkedOldResource tail head ktail khead π (W∪R.active.rowSet) B e)∧
      (∀ v∈C.rows\R.active.rowSet,∀ w∈C.rows\R.active.rowSet,v≠w→¬PermutationClose π b v w)∧
      ∀ v∈C.rows\R.active.rowSet,∀ w∈R.active.rowSet,¬PermutationClose π b v w:=by
  obtain ⟨ε,hε,habs⟩:=marked_relative_active_host_absorber l hl ρ σ q₀ β blo bhi hρ hσ hq₀ hβ hblo hbhi
  refine ⟨ε,hε,?_⟩
  intro s
  obtain ⟨a₀,b₀,habs⟩:=habs s
  refine ⟨a₀,b₀,?_⟩
  intro f b dF hdF
  obtain ⟨N,habs⟩:=habs (5*f) b dF hdF
  refine ⟨N,?_⟩
  intro V₀ U₀ V U E K A S _ _ _ _ _ _ _ _ _ _ _ _ hn tail head ktail khead H₀ HK π hb G hG hsize R W B F₀ hf₀ hpair hRH Q hp hB hW F hconf htypes hF Profiles
  let Z₀:=markedForbiddenResourceRows π F₀
  let B₀:=markedForbiddenResourceHubs F₀
  have hZ:Z₀.card≤4*f:=(marked_forbidden_resource_rows_card F₀ hpair).trans (Nat.mul_le_mul_left _ hf₀)
  have hBh:B₀.card≤f:=(marked_forbidden_resource_hubs_card F₀).trans hf₀
  have hW':((W∪Z₀).card:ℝ)≤ε*Fintype.card V+(5*f:ℕ):=by
    have hu:((W∪Z₀).card:ℝ)≤W.card+Z₀.card:=by exact_mod_cast Finset.card_union_le W Z₀
    have hz:(Z₀.card:ℝ)≤4*f:=by exact_mod_cast hZ
    push_cast
    linarith only [hu,hz,hW]
  have hB':((B∪B₀).card:ℝ)≤ε*Fintype.card V+(5*f:ℕ):=by
    have hu:((B∪B₀).card:ℝ)≤B.card+B₀.card:=by exact_mod_cast Finset.card_union_le B B₀
    have hb₀:(B₀.card:ℝ)≤f:=by exact_mod_cast hBh
    push_cast
    nlinarith only [hu,hb₀,hB,(Nat.cast_nonneg f:0≤(f:ℝ))]
  obtain ⟨C,habsC,hrows,hhubs,hWavoid,hBavoid,hOld,hsep,hroot⟩:=
    habs V₀ U₀ V U E K A S hn tail head ktail khead H₀ HK π hb G hG hsize R (W∪Z₀) (B∪B₀)
      (fun u=>Finset.mem_union_left _ (hRH u)) Q hp hB' hW' F hconf htypes hF Profiles
  have hdis:Disjoint C.edges F₀:=by
    apply marked_no_old_resources_disjoint_finite F₀ C.edges ((W∪Z₀)∪R.active.rowSet) (B∪B₀)
      (Finset.subset_union_right.trans Finset.subset_union_left) Finset.subset_union_right hOld
    intro e he
    cases e with
    | inl e=>obtain ⟨a,ha,_,_⟩:=C.supported _ he;exact ⟨a,ha⟩
    | inr vu=>trivial
  refine ⟨C,habsC,hdis,hrows,hhubs,?_,?_,?_,hsep,hroot⟩
  · intro v hv hw
    exact hWavoid v hv ((Finset.union_subset_union Finset.subset_union_left (Finset.Subset.refl _)) hw)
  · intro u hu hb
    exact hBavoid u hu (Finset.mem_union_left _ hb)
  · intro e he ho
    exact hOld e he (marked_old_resource_mono
      (Finset.union_subset_union Finset.subset_union_left (Finset.Subset.refl _)) Finset.subset_union_left e ho)

end Oberwolfach
