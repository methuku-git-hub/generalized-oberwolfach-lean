module

public import Oberwolfach.MarkedAssignedRowAfterDeletion
public import Oberwolfach.MarkedRowRimClassification
public import Oberwolfach.MarkedFreeRowLoads
public import Oberwolfach.MarkedFreeRimDisjointness

@[expose] public section

/-! Pack the wheels through one prescribed row. Only the union of free
physical rim edges is deleted in subsequent path choices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E T : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head : E → V} {ktail khead : T → V} {H₀ HK : V → U → Prop}
    {π : Equiv.Perm V} {b l : ℕ} {c ch : ℝ}

theorem marked_assigned_row_packing
    (Q : MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (hl : 2≤l) (hb : 1≤b) (X : Finset V) (hX : ∀ x, π x∈X ↔ x∈X)
    (v : V) (hv : v∉X) (N K D₀ : ℕ) (hK : 0<K)
    (a z : Fin N → V) (u : Fin N → U) (jin jout : Fin N → Bool)
    (hu : Function.Injective u) (ha : ∀ i, a i∈X) (hz : ∀ i, z i∈X)
    (htypes : ∀ i, ¬(jin i=true ∧ jout i=true))
    (haz : ∀ i, ¬PermutationClose π b (a i) (z i))
    (hav : ∀ i, ¬PermutationClose π b (a i) v) (hzv : ∀ i, ¬PermutationClose π b (z i) v)
    (haH : ∀ i, if jout i then HK (a i) (u i) else H₀ (a i) (u i))
    (hzH : ∀ i, H₀ (z i) (u i))
    (hroot : ∀ i, if jin i then HK v (u i) else H₀ v (u i))
    (hopen : ∀ i, markedArcPresent tail head ktail khead (jout i) v (a i))
    (hclose : ∀ i, markedArcPresent tail head ktail khead (jin i) (z i) v)
    (hroots : ∀ i j, i≠j → Disjoint (markedRowRootRims π v (a i) (z i) (jin i) (jout i))
      (markedRowRootRims π v (a j) (z j) (jin j) (jout j)))
    (hend : ∀ x, (Finset.univ.filter (fun i => x=a i ∨ x=z i)).card≤D₀)
    (hbudget : ((Xᶜ).card:ℝ)+(N*(l+4):ℕ)/(K:ℝ)+(l+5)*(2*b+1)+8*(K+D₀:ℕ)<c) :
    ∃ C : Fin N → MarkedWheel tail head ktail khead (l+3) π b H₀ HK,
      (∀ i, (C i).2.val=u i ∧ ∃ p : Fin (l+3) ↪ V,
        p 0=a i ∧ p (Fin.last (l+2))=z i ∧
        (∀ j, (C i).1.val j=Fin.cons (α:=fun _=>V) v p (markedAssignedRowOrder (l+3) (jin i) (jout i) j)) ∧
        ∀ j, p j∈X) ∧
      (∀ i j, i≠j → Disjoint (markedWheelPhysicalResources (C i)) (markedWheelPhysicalResources (C j))) ∧
      (∀ x∈X, markedFamilyFreeRowLoad C a z x≤K) ∧
      (∀ x, (spanningRestriction (markedFamilyRim C) X).degree x≤4*(K+D₀)) ∧
      (∀ x∈X, (Finset.univ.filter (markedFamilySpokes C x)).card≤K+D₀) ∧
      (∀ w, (Finset.univ.filter (fun x => markedFamilySpokes C x w)).card≤l+4) := by
  let Good (i : Fin N) (C : MarkedWheel tail head ktail khead (l+3) π b H₀ HK) :=
    C.2.val=u i ∧ ∃ p : Fin (l+3) ↪ V,
      p 0=a i ∧ p (Fin.last (l+2))=z i ∧
      (∀ j, C.1.val j=Fin.cons (α:=fun _=>V) v p (markedAssignedRowOrder (l+3) (jin i) (jout i) j)) ∧
      ∀ j, p j∈X
  have forced_bound {k : ℕ} (e : Fin k ↪ Fin N) (x : V) :
      (Finset.univ.filter (fun j => x=a (e j) ∨ x=z (e j))).card≤D₀ := by
    apply le_trans _ (hend x)
    apply Finset.card_le_card_of_injOn e
    · intro j hj; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hj).2⟩
    · intro i _ j _ hij; exact e.injective hij
  have classify {i : Fin N} {C : MarkedWheel tail head ktail khead (l+3) π b H₀ HK}
      (hC : Good i C) :
      ∀ e∈markedCyclePhysicalEdges tail head ktail khead (l+3) π b C.1,
        e⊆X ∨ e∈markedRowRootRims π v (a i) (z i) (jin i) (jout i) := by
    obtain ⟨hCu,p,hp0,hplast,hp,hpX⟩ := hC
    have hh := marked_assigned_row_rim_classification (by omega : 2≤l+2) p v (jin i) (jout i)
      (htypes i) X (fun x hx => (hX x).mpr hx) hpX C hp
    simpa only [hp0,hplast] using hh
  have hp : ∀ k : ℕ, ∀ hk : k≤N,
      ∃ C : Fin k → MarkedWheel tail head ktail khead (l+3) π b H₀ HK,
      (∀ j, Good ⟨j.val,lt_of_lt_of_le j.isLt hk⟩ (C j)) ∧
      (∀ i j, i≠j → Disjoint (markedWheelPhysicalResources (C i)) (markedWheelPhysicalResources (C j))) ∧
      ∀ x∈X, markedFamilyFreeRowLoad C
        (fun j => a ⟨j.val,lt_of_lt_of_le j.isLt hk⟩)
        (fun j => z ⟨j.val,lt_of_lt_of_le j.isLt hk⟩) x≤K := by
    intro k
    induction k with
    | zero =>
      intro hk
      refine ⟨Fin.elim0,fun j => Fin.elim0 j,fun i => Fin.elim0 i,?_⟩
      intro x hx; simp [markedFamilyFreeRowLoad]
    | succ k ih =>
      intro hk
      have hkN : k≤N := by omega
      obtain ⟨C,hC,hdis,hcap⟩ := ih hkN
      let e : Fin k ↪ Fin N := ⟨fun j => ⟨j.val,lt_of_lt_of_le j.isLt hkN⟩,
        by intro a b h; exact Fin.ext (congrArg (fun z : Fin N => z.val) h)⟩
      let i : Fin N := ⟨k,by omega⟩
      let D := spanningRestriction (markedFamilyRim C) X
      let S := Finset.univ.filter (fun x => K≤markedFamilyFreeRowLoad C (a ∘ e) (z ∘ e) x)
      let W := (Xᶜ∪S) \ {a i,z i}
      have hS : (S.card:ℝ)≤(N*(l+4):ℕ)/(K:ℝ) := by
        apply (le_div_iff₀ (Nat.cast_pos.mpr hK)).mpr
        have hh : K*S.card≤N*(l+4) := (markedFamilyFreeRowLoad_saturated C (a ∘ e) (z ∘ e) K).trans
          (by simp only [Fintype.card_fin]; exact Nat.mul_le_mul_right (l+4) hkN)
        exact_mod_cast (by simpa only [Nat.mul_comm] using hh)
      have hW : (W.card:ℝ)≤((Xᶜ).card:ℝ)+(N*(l+4):ℕ)/(K:ℝ) := by
        have hh : (W.card:ℝ)≤(Xᶜ).card+S.card := by
          exact_mod_cast (Finset.card_le_card Finset.sdiff_subset).trans (Finset.card_union_le (Xᶜ) S)
        linarith only [hh,hS]
      have hD : ∀ x, (D.degree x:ℝ)≤4*(K+D₀:ℕ) := by
        intro x
        have hh := marked_free_rim_degree C (a ∘ e) (z ∘ e) hb X hX K D₀ hcap (forced_bound e) x
        exact_mod_cast hh
      have haW : a i∉W := by simp [W]
      have hzW : z i∉W := by simp [W]
      have haZ : a i∉({v}:Finset V) := by
        intro h
        exact hv ((Finset.mem_singleton.mp h) ▸ ha i)
      have hzZ : z i∉({v}:Finset V) := by
        intro h
        exact hv ((Finset.mem_singleton.mp h) ▸ hz i)
      have hoD : ¬D.Adj v (if jout i then π (a i) else a i) := by
        intro h; exact hv ((spanningRestriction_adj _ _ _ _).mp h).2.1
      have hcD : ¬D.Adj (z i) (if jin i then π v else v) := by
        intro h
        have hh := ((spanningRestriction_adj _ _ _ _).mp h).2.2
        cases hji : jin i
        · rw [hji] at hh; exact hv hh
        · rw [hji] at hh; exact hv ((hX v).mp hh)
      obtain ⟨p,B,hp0,hplast,hBu,hB,havB,hsep,hBD⟩ := marked_assigned_row_after_deletion Q hl D
        (4*(K+D₀:ℕ)) (by positivity) hD v (a i) (z i) (u i) (jin i) (jout i) (htypes i)
        W {v} (by simp) haW hzW haZ hzZ (haz i)
        (by intro x hx; rw [Finset.mem_singleton.mp hx]; exact hav i)
        (by intro x hx; rw [Finset.mem_singleton.mp hx]; exact hzv i)
        (haH i) (hzH i) (hroot i) (hopen i) (hclose i) hoD hcD
        (by simp only [Finset.card_singleton,Nat.cast_one]; linarith only [hW,hbudget])
      have hpX : ∀ j, p j∈X := by
        intro j
        by_contra hx
        apply (havB j).1
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_union_left _ (Finset.mem_compl.mpr hx),?_⟩
        intro h
        rcases Finset.mem_insert.mp h with he|he
        · exact hx (he ▸ ha i)
        · exact hx ((Finset.mem_singleton.mp he) ▸ hz i)
      have hBG : Good i B := ⟨hBu,p,hp0,hplast,hB,hpX⟩
      have hcross : ∀ j, Disjoint (markedWheelPhysicalResources (C j)) (markedWheelPhysicalResources B) := by
        apply marked_free_rim_extension_disjoint (by omega) hb C B X
          (fun j => markedRowRootRims π v (a (e j)) (z (e j)) (jin (e j)) (jout (e j)))
          (markedRowRootRims π v (a i) (z i) (jin i) (jout i))
        · intro j; exact classify (hC j)
        · exact classify hBG
        · intro j; exact marked_row_root_rim_not_inside X hX v _ _ hv _ _
        · intro j; apply hroots (e j) i
          intro he; have hh := congrArg (fun z : Fin N => z.val) he
          have hj := j.isLt; dsimp [e,i] at hh; omega
        · intro j h
          have he := hu ((hC j).1.symm.trans (h.trans hBu))
          have hh := congrArg (fun z : Fin N => z.val) he
          have hj := j.isLt; dsimp [e,i] at hh; omega
        · exact hBD
      refine ⟨Fin.snoc C B,?_,?_,?_⟩
      · intro j
        refine Fin.lastCases ?_ (fun j => ?_) j
        · simpa only [Fin.snoc_last,Fin.val_last,i] using hBG
        · simpa only [Fin.snoc_castSucc,Fin.val_castSucc] using hC j
      · intro j q
        refine Fin.lastCases ?_ (fun j' => ?_) j
        · refine Fin.lastCases ?_ (fun q' => ?_) q
          · intro h; exact (h rfl).elim
          · intro _; simpa only [Fin.snoc_last,Fin.snoc_castSucc] using (hcross q').symm
        · refine Fin.lastCases ?_ (fun q' => ?_) q
          · intro _; simpa only [Fin.snoc_last,Fin.snoc_castSucc] using hcross j'
          · intro h; simpa only [Fin.snoc_castSucc] using hdis j' q' (fun he => h (congrArg Fin.castSucc he))
      · intro x hx
        have haeq : (fun j : Fin (k+1) => a ⟨j.val,lt_of_lt_of_le j.isLt hk⟩)=Fin.snoc (a ∘ e) (a i) := by
          funext j; refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [e,i]
        have hzeq : (fun j : Fin (k+1) => z ⟨j.val,lt_of_lt_of_le j.isLt hk⟩)=Fin.snoc (z ∘ e) (z i) := by
          funext j; refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [e,i]
        rw [haeq,hzeq,markedFamilyFreeRowLoad_snoc]
        by_cases hfree : x∈markedWheelRows B ∧ x≠a i ∧ x≠z i
        · rw [if_pos hfree]
          have hxS : x∉S := by
            intro hs
            rw [marked_one_root_rows p v _ B hB] at hfree
            rcases Finset.mem_insert.mp hfree.1 with h|h
            · exact hv (h ▸ hx)
            · obtain ⟨j,hj,he⟩ := Finset.mem_image.mp h
              apply (havB j).1
              rw [he]
              exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ hs,by simpa using hfree.2⟩
          have hh : markedFamilyFreeRowLoad C (a ∘ e) (z ∘ e) x<K := by
            simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and,not_le] using hxS
          omega
        · rw [if_neg hfree,Nat.add_zero]; exact hcap x hx
  obtain ⟨C,hC,hdis,hcap⟩ := hp N le_rfl
  refine ⟨C,hC,hdis,hcap,marked_free_rim_degree C a z hb X hX K D₀ hcap hend,?_,?_⟩
  · intro x hx
    exact (markedFamilySpokes_row C x).trans ((markedFamilyRowLoad_le_free_add_forced C a z x).trans
      (Nat.add_le_add (hcap x hx) (hend x)))
  · intro w
    have hh : markedFamilyHubLoad C w≤1 := by
      apply Finset.card_le_one.mpr
      intro i hi j hj
      apply hu
      exact (hC i).1.symm.trans ((Finset.mem_filter.mp hi).2.trans
        ((Finset.mem_filter.mp hj).2.symm.trans (hC j).1))
    exact (markedFamilySpokes_column C w).trans (by simpa using Nat.mul_le_mul_right (l+4) hh)

end Oberwolfach
