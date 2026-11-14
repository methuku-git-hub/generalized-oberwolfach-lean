module

public import Oberwolfach.EndpointHostGraph
public import Oberwolfach.EndpointRelativeCounts

@[expose] public section

/-! The endpoint common-neighbourhood inputs follow from the manuscript's
row and index inequalities on their original domains. Only the singleton
and three-row index inequalities are used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 4500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

def endpointCountCoefficient (p κ : ℝ) : ℝ := min (p^4/16) (κ*p^3/2)

theorem endpointCountCoefficient_pos (p κ : ℝ) (hp : 0<p) (hκ : 0<κ) :
    0<endpointCountCoefficient p κ := by unfold endpointCountCoefficient;positivity

theorem endpoint_source_counts (P R H F : SimpleGraph V) (A B : Finset V) (x : V)
    (hAB : Disjoint A B) (hR : R≤P\F)
    (p q s ε L κ : ℝ) (hp : 0<p) (hp1 : p≤1) (hq : p≤q) (hs : p≤s)
    (hκ : 0<κ) (hB : κ*A.card≤(B.card:ℝ)) (hL : 0≤L) (hLa : L≤(A.card:ℝ)/24)
    (hε : ε≤min (p^4/16) (p^3/2))
    (hdeg : ∀ v∈insert x A,(3/4:ℝ)*A.card≤((A∩P.neighborFinset v).card:ℝ))
    (hF : ∀ v,(F.degree v:ℝ)≤L)
    (hrows : ∀ X J : Finset V,x∈X → X⊆insert x A → J⊆B →
      X.card≤3 → J.card≤2 → X.card+J.card≤4 →
      q^X.card*s^J.card*((common A X (fun v=>(P\F).neighborFinset v)).card:ℝ)-ε*A.card≤
        ((common (common A X (fun v=>R.neighborFinset v)) J (fun v=>H.neighborFinset v)).card:ℝ))
    (hindices : ∀ X : Finset V,x∈X → X⊆insert x A → (X.card=1 ∨ X.card=3) →
      (∀ v∈X,∀ w∈X,¬F.Adj v w) →
      (s^X.card-ε)*B.card≤((common B X (fun v=>H.neighborFinset v)).card:ℝ)) :
    EndpointNeighbourCounts (endpointHostGraph R H A B) F
      (common A {x} (fun v=>R.neighborFinset v)) (common B {x} (fun v=>H.neighborFinset v))
      (endpointCountCoefficient p κ*A.card) := by
  let S := common A {x} (fun v=>R.neighborFinset v)
  let T := common B {x} (fun v=>H.neighborFinset v)
  have hSA : S⊆A := fun v hv=>((mem_common_iff _ _ _ _).mp hv).1
  have hTB : T⊆B := fun v hv=>((mem_common_iff _ _ _ _).mp hv).1
  have hSx (v : V) (hv : v∈S) : R.Adj x v := by
    simpa only [Finset.mem_singleton,forall_eq,SimpleGraph.mem_neighborFinset] using ((mem_common_iff _ _ _ _).mp hv).2
  have hSF (v : V) (hv : v∈S) : ¬F.Adj x v := (hR (hSx v hv)).2
  have hscale : endpointCountCoefficient p κ*A.card≤(p^3/2)*B.card := by
    calc
      _ ≤ (κ*p^3/2)*A.card := mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg _)
      _ = (p^3/2)*(κ*A.card) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hB (by positivity)
  constructor
  · apply hscale.trans
    apply endpoint_relative_index_lower H B {x} p s ε hp hp1 hs (by simp)
      (hε.trans (min_le_right _ _))
    apply hindices {x} (by simp) (by simp) (Or.inl (by simp))
    intro v hv w hw
    simp only [Finset.mem_singleton] at hv hw
    subst v;subst w;exact F.loopless.irrefl x
  · intro Y J hY hJ hYc hJc hYJ
    rw [endpointHostGraph_row_common R H A B hAB x Y J hY (hJ.trans hTB)]
    have hXY : insert x Y⊆insert x A := Finset.insert_subset_insert x (hY.trans hSA)
    have hcard : (insert x Y).card≤3 := (Finset.card_insert_le _ _).trans (by omega)
    have hcardJ : (insert x Y).card+J.card≤4 := by have hh:=Finset.card_insert_le x Y;omega
    have hh := endpoint_relative_row_lower P R H F A (insert x Y) J p q s ε L hp hp1 hq hs
      hcard hcardJ hL hLa (hε.trans (min_le_left _ _))
      (fun v hv=>hdeg v (hXY hv)) (fun v _=>hF v)
      (hrows _ _ (by simp) hXY (hJ.trans hTB) hcard hJc hcardJ)
    exact (mul_le_mul_of_nonneg_right (min_le_left (p^4/16) (κ*p^3/2)) (Nat.cast_nonneg _)).trans hh
  · intro v hv w hw hvw hvwF
    rw [endpointHostGraph_index_common R H A B hAB x {v,w}
      (by simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff];exact ⟨hSA hv,hSA hw⟩)]
    have hxv : x≠v := (hSx v hv).ne
    have hxw : x≠w := (hSx w hw).ne
    have hcard : (insert x {v,w}:Finset V).card=3 := by simp [hxv,hxw,hvw]
    have hX : insert x {v,w}⊆insert x A := by
      apply Finset.insert_subset_insert
      simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
      exact ⟨hSA hv,hSA hw⟩
    have hfree : ∀ z∈insert x ({v,w}:Finset V),∀ z'∈insert x ({v,w}:Finset V),¬F.Adj z z' := by
      have hxvF := hSF v hv
      have hxwF := hSF w hw
      have hvxF : ¬F.Adj v x := fun h=>hxvF h.symm
      have hwxF : ¬F.Adj w x := fun h=>hxwF h.symm
      have hwvF : ¬F.Adj w v := fun h=>hvwF h.symm
      intro z hz z' hz'
      simp only [Finset.mem_insert,Finset.mem_singleton] at hz hz'
      rcases hz with rfl|rfl|rfl <;> rcases hz' with rfl|rfl|rfl <;> simp_all
    exact hscale.trans (endpoint_relative_index_lower H B (insert x {v,w}) p s ε hp hp1 hs
      hcard.le (hε.trans (min_le_right _ _)) (hindices _ (by simp) hX (Or.inr hcard) hfree))

end Oberwolfach
