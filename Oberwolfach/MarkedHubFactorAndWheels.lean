module

public import Oberwolfach.HubNeighbourClasses
public import Oberwolfach.HubFactorWeightScales
public import Oberwolfach.MarkedFactorPhysical

@[expose] public section

/-! The one-hub marked local-factor lemma, with ambient-normalized original
weights, exact spoke coverage, distinct physical rim edges, and degree two.
No invariance of a hub neighbourhood under the successor is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 256
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_hub_factor_and_wheels (m : ℕ) (hm : 3<m+1) (β bLo bHi : ℝ)
    (hβ : 0<β) (hbLo : 0<bLo) (hbHi : 0≤bHi) :
    ∃ η : ℝ,0<η ∧ ∃ N : ℕ,∀ (A U E K : Type) [Fintype A] [DecidableEq A] [DecidableEq U],
      N≤Fintype.card A →
      ∀ (tail head : E → A) (ktail khead : K → A) (π : Equiv.Perm A)
        (b : ℕ) (H₀ Hₖ : A → U → Prop) (w : U),1≤b →
      Function.Injective (markedPhysicalEdge tail head ktail khead π) →
      (∀ v,¬(H₀ v w ∧ Hₖ v w)) →
      (∀ v z,H₀ v w → Hₖ z w → v≠π z) →
      β*Fintype.card A≤Fintype.card (hubNeighbourClass H₀ Hₖ w true) →
      Fintype.card (hubNeighbourClass H₀ Hₖ w false)=m*Fintype.card (hubNeighbourClass H₀ Hₖ w true) →
      β*(Fintype.card A:ℝ)^(m+1)≤Fintype.card (HubMarkedCycle tail head ktail khead m π b H₀ Hₖ w) →
      (∀ j : Bool,∀ v v' : A,v≠v' →
        (if j then Hₖ v w else H₀ v w) → (if j then Hₖ v' w else H₀ v' w) →
        β*(Fintype.card A:ℝ)^m≤Fintype.card (RootFirstCommonMarkedPath tail head ktail khead m π b H₀ Hₖ j v v' w w)) →
      ∀ wt : HubMarkedCycle tail head ktail khead m π b H₀ Hₖ w → ℝ,
      (∀ C,bLo/(Fintype.card A:ℝ)^m≤wt C ∧ wt C≤bHi/(Fintype.card A:ℝ)^m) →
      (∀ v,H₀ v w ∨ Hₖ v w → |1-hypergraphWeightedDegree (hubMarkedCycleVertices w) wt v|≤η) →
      ∃ M : Finset (HubMarkedCycle tail head ktail khead m π b H₀ Hₖ w),
        (∀ C∈M,∀ D∈M,C≠D → Disjoint (hubMarkedCycleVertices w C) (hubMarkedCycleVertices w D)) ∧
        M.biUnion (hubMarkedCycleVertices w)=Finset.univ.filter (fun v => H₀ v w ∨ Hₖ v w) ∧
        (∀ v,H₀ v w ∨ Hₖ v w → ∃! C : M,Sum.inr (v,w)∈markedWheelPhysicalResources (hubCycleWheel w C.val)) ∧
        (∀ C∈M,∀ D∈M,C≠D → Disjoint (hubCyclePhysicalEdges w C) (hubCyclePhysicalEdges w D)) ∧
        (∀ C∈M,∀ e∈hubCyclePhysicalEdges w C,e.card=2) ∧
        ∀ v,(physicalEdgeGraph (M.biUnion (hubCyclePhysicalEdges w))).degree v≤2 := by
  obtain ⟨η,hη,k₀,hfactor⟩ := marked_hub_factor m hm β (bLo*β^m) bHi hβ (by positivity) hbHi
  obtain ⟨N,hN⟩ := exists_nat_gt (max (1:ℝ) ((k₀:ℝ)/β))
  refine ⟨η,hη,N,?_⟩
  intro A U E K _ _ _ hn tail head ktail khead π b H₀ Hₖ w hb hp hd hsep hsize hratio hbase hpath wt hw herr
  let V := hubNeighbourClass H₀ Hₖ w
  let k := Fintype.card (V true)
  let e := hubNeighbourEmbedding H₀ Hₖ w hd
  have hNn : (N:ℝ)≤Fintype.card A := by exact_mod_cast hn
  have hnpos : (0:ℝ)<Fintype.card A := by linarith [le_max_left (1:ℝ) ((k₀:ℝ)/β)]
  have hkpos : (0:ℝ)<k := (mul_pos hβ hnpos).trans_le hsize
  have hk₀ : k₀≤k := by
    have hh : (k₀:ℝ)/β≤Fintype.card A := (le_max_right _ _).trans (hN.le.trans hNn)
    have hkk : (k₀:ℝ)≤k := by linarith [(div_le_iff₀ hβ).mp hh]
    exact_mod_cast hkk
  have hkn : (k:ℝ)≤Fintype.card A := by
    exact_mod_cast (Fintype.card_le_of_injective (fun v : V true => v.val) Subtype.val_injective)
  have hclasses (i : Bool) : Fintype.card (V i)=twoClassProfile m i*k := by
    cases i
    · exact hratio
    · simp [twoClassProfile,k]
  have hwt (C) : (bLo*β^m)/(k:ℝ)^m≤wt C ∧ wt C≤bHi/(k:ℝ)^m :=
    hub_factor_weight_scale m _ _ β bLo bHi (wt C) hnpos hkpos hβ hbLo.le hbHi hkn hsize (hw C)
  have herr' (v : Σ i,V i) : |1-hypergraphWeightedDegree (hubMarkedCycleVertices w) wt (e v)|≤η := by
    apply herr
    rcases v with ⟨i,v⟩
    cases i
    · exact Or.inl v.property
    · exact Or.inr v.property
  obtain ⟨M,hM,hU⟩ := hfactor k hk₀ V A U E K hclasses e tail head ktail khead π b H₀ Hₖ w
    (hubNeighbourEmbedding_type H₀ Hₖ w hd true) (hubNeighbourEmbedding_type H₀ Hₖ w hd false)
    hbase hpath wt hwt herr'
  rw [hubNeighbourEmbedding_image] at hU
  refine ⟨M,hM,hU,?_,marked_factor_physical_edges_disjoint w hp M hM,?_,
    marked_factor_physical_degree w hsep M hM⟩
  · intro v hv
    apply marked_factor_physical_spoke_once w M hM v
    rw [hU]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩
  · intro C hC e he
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp he
    exact markedCycle_physical_edge_card tail head ktail khead m π b (by omega) hb (hubCycleAsMarked w C) j

end Oberwolfach
