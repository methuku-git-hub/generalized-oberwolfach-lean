module

public import Oberwolfach.FiniteMaximalPairing
public import Oberwolfach.ColourRetentionCoins

@[expose] public section

/-! Simultaneous conflict witnesses with bounded multiplicity. A maximal
matching pairs some direct witnesses; the unmatched witnesses are
independent, so local independence bounds control every remaining load. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem bounded_monochromatic_conflict_witnesses
    {V C : Type*} [Fintype V] (G : SimpleGraph V) (D : Finset V)
    (σ : V → C×Bool) (c : C) {k : ℕ}
    (hlocal : ∀ (w : V) (S : Finset V),
      (∀ v∈S,G.Adj w v) →
      (∀ u∈S,∀ v∈S,u≠v → ¬G.Adj u v) → S.card≤k)
    (hcolour : ∀ v∈D,(σ v).1=c)
    (hbad : ∀ v∈D,¬coinColourSurvives G σ v) :
    ∃ f : V → V,
      (∀ v∈D,(σ (f v)).1=c ∧
        ((f v=v ∧ (σ v).2≠true) ∨ G.Adj v (f v))) ∧
      (∀ w,(D.filter (fun v=>f v=w)).card≤k+2) := by
  classical
  obtain ⟨m,hm,hind⟩ := finite_maximal_pairing G D
  have hconf (v : V) (hv : v∈D) (hcoin : (σ v).2=true) :
      ∃ u,G.Adj v u ∧ (σ u).1=(σ v).1 := by
    by_contra hn
    apply hbad v hv
    refine ⟨hcoin,?_⟩
    intro u hu he
    exact hn ⟨u,hu,he⟩
  let f : V → V := fun v=>match m v with
    | some u=>u
    | none=>if h : v∈D ∧ (σ v).2=true then
        Classical.choose (hconf v h.1 h.2) else v
  have hsome (v u : V) (h : m v=some u) : f v=u := by simp [f,h]
  have hspec (v : V) (hv : v∈D) :
      (σ (f v)).1=c ∧ ((f v=v ∧ (σ v).2≠true) ∨ G.Adj v (f v)) := by
    cases hmv : m v with
    | some u =>
      rw [hsome v u hmv]
      exact ⟨hcolour u (hm v u hmv).2.1,Or.inr (hm v u hmv).2.2.1⟩
    | none =>
      by_cases hc : (σ v).2=true
      · have h : v∈D ∧ (σ v).2=true := ⟨hv,hc⟩
        have he : f v=Classical.choose (hconf v h.1 h.2) := by simp [f,hmv,h]
        rw [he]
        have hw := Classical.choose_spec (hconf v h.1 h.2)
        exact ⟨hw.2.trans (hcolour v hv),Or.inr hw.1⟩
      · have he : f v=v := by simp [f,hmv,hc]
        rw [he]
        exact ⟨hcolour v hv,Or.inl ⟨rfl,hc⟩⟩
  refine ⟨f,hspec,?_⟩
  intro w
  let F := D.filter (fun v=>f v=w)
  let P := F.filter (fun v=>m v≠none)
  let U := F.filter (fun v=>m v=none ∧ v≠w)
  have hP : P.card≤1 := by
    apply Finset.card_le_one.mpr
    intro u hu v hv
    have huF := Finset.mem_filter.mp hu
    have hvF := Finset.mem_filter.mp hv
    have huf : f u=w := (Finset.mem_filter.mp huF.1).2
    have hvf : f v=w := (Finset.mem_filter.mp hvF.1).2
    have hum : m u=some w := by
      cases hmu : m u with
      | none => exact False.elim (huF.2 hmu)
      | some z =>
        have hzw : z=w := (hsome u z hmu).symm.trans huf
        simpa only [hzw] using hmu
    have hvm : m v=some w := by
      cases hmv : m v with
      | none => exact False.elim (hvF.2 hmv)
      | some z =>
        have hzw : z=w := (hsome v z hmv).symm.trans hvf
        simpa only [hzw] using hmv
    exact Option.some.inj ((hm u w hum).2.2.2.symm.trans (hm v w hvm).2.2.2)
  have hU : U.card≤k := by
    apply hlocal w U
    · intro v hv
      obtain ⟨hvF,hmv,hvw⟩ := Finset.mem_filter.mp hv
      obtain ⟨hvD,hfv⟩ := Finset.mem_filter.mp hvF
      rcases (hspec v hvD).2 with hself|hadj
      · exact False.elim (hvw (hself.1.symm.trans hfv))
      · exact (hfv ▸ hadj).symm
    · intro u hu v hv _hne
      obtain ⟨huF,hmu,_⟩ := Finset.mem_filter.mp hu
      obtain ⟨hvF,hmv,_⟩ := Finset.mem_filter.mp hv
      exact hind u (Finset.mem_filter.mp huF).1 v (Finset.mem_filter.mp hvF).1 hmu hmv
  have hcover : F⊆(P∪U)∪{w} := by
    intro v hv
    by_cases hmnone : m v=none
    · by_cases he : v=w
      · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr he)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hv,hmnone,he⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hv,hmnone⟩))
  have hcard : F.card≤P.card+U.card+1 :=
    (Finset.card_le_card hcover).trans
      ((Finset.card_union_le _ _).trans (by
        simpa only [Finset.card_singleton] using
          Nat.add_le_add_right (Finset.card_union_le P U) 1))
  change F.card≤_
  omega

end Oberwolfach
