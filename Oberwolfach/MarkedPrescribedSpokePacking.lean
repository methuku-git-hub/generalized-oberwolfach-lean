module

public import Oberwolfach.MarkedSpokeAfterDeletion

@[expose] public section

/-! Prescribed-spoke cover-down in a marked host. All additional auxiliary
rows lie in X. Physical rim degrees charge both a row and its inverse
permutation image. Prescribed spokes may repeat a row or hub, but not a pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E T:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:T→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ} {c ch:ℝ}

theorem marked_prescribed_spoke_wheel_packing
    (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (hl:2≤l) (hb:1≤b) (X:Finset V) (N K D₀:ℕ) (hK:0<K)
    (x:Fin N→V) (u:Fin N→U) (t:Fin N→Bool) (hx:∀ i,x i∉X)
    (hH:∀ i,if t i then HK (x i) (u i) else H₀ (x i) (u i))
    (hedge:Function.Injective (fun i=>(x i,u i)))
    (hend:∀ a,(Finset.univ.filter (fun i=>a=x i)).card≤D₀)
    (hhub:∀ v,(Finset.univ.filter (fun i=>u i=v)).card≤D₀)
    (hbudget:((Xᶜ).card:ℝ)+(N*(l+4):ℕ)/(K:ℝ)+(D₀*(l+4):ℕ)+
      (l+5)*(2*b+1)+8*(K+D₀:ℕ)<c):
    ∃ C:Fin N→MarkedWheel tail head ktail khead (l+3) π b H₀ HK,
      (∀ i,(C i).2.val=u i ∧ x i∈markedWheelRows (C i) ∧
        ∀ a∈markedWheelRows (C i),a=x i∨a∈X) ∧
      (∀ i j,i≠j→Disjoint (markedWheelPhysicalResources (C i)) (markedWheelPhysicalResources (C j))) ∧
      (∀ a∈X,markedFamilyRowLoad C a≤K) ∧
      (∀ a,(markedFamilyRim C).degree a≤4*(K+D₀)) ∧
      (∀ a,(Finset.univ.filter (markedFamilySpokes C a)).card≤K+D₀) ∧
      (∀ v,(Finset.univ.filter (fun a=>markedFamilySpokes C a v)).card≤D₀*(l+4)):=by
  let Good (i:Fin N) (C:MarkedWheel tail head ktail khead (l+3) π b H₀ HK):=
    C.2.val=u i ∧ x i∈markedWheelRows C ∧ ∀ a∈markedWheelRows C,a=x i∨a∈X
  have load_bound {k:ℕ} (e:Fin k↪Fin N) (C:Fin k→MarkedWheel tail head ktail khead (l+3) π b H₀ HK)
      (hC:∀ j,Good (e j) (C j)) (hcap:∀ a∈X,markedFamilyRowLoad C a≤K) (a:V):
      markedFamilyRowLoad C a≤K+D₀:=by
    by_cases ha:a∈X
    · exact (hcap a ha).trans (Nat.le_add_right _ _)
    · have hh:markedFamilyRowLoad C a≤(Finset.univ.filter (fun i=>a=x i)).card:=by
        apply Finset.card_le_card_of_injOn e
        · intro j hj
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
          rcases (hC j).2.2 a (Finset.mem_filter.mp hj).2 with h|h
          · exact h
          · exact (ha h).elim
        · intro i _ j _ hij;exact e.injective hij
      exact (hh.trans (hend a)).trans (Nat.le_add_left _ _)
  have hub_bound {k:ℕ} (e:Fin k↪Fin N) (C:Fin k→MarkedWheel tail head ktail khead (l+3) π b H₀ HK)
      (hC:∀ j,Good (e j) (C j)) (v:U):markedFamilyHubLoad C v≤D₀:=by
    apply le_trans _ (hhub v)
    apply Finset.card_le_card_of_injOn e
    · intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hC j).1.symm.trans (Finset.mem_filter.mp hj).2⟩
    · intro i _ j _ hij;exact e.injective hij
  have hp:∀ k:ℕ,∀ hk:k≤N,∃ C:Fin k→MarkedWheel tail head ktail khead (l+3) π b H₀ HK,
      (∀ j,Good ⟨j.val,lt_of_lt_of_le j.isLt hk⟩ (C j)) ∧
      (∀ i j,i≠j→Disjoint (markedWheelPhysicalResources (C i)) (markedWheelPhysicalResources (C j))) ∧
      ∀ a∈X,markedFamilyRowLoad C a≤K:=by
    intro k
    induction k with
    | zero=>
      intro hk
      refine ⟨Fin.elim0,fun j=>Fin.elim0 j,fun i=>Fin.elim0 i,?_⟩
      intro a _;simp [markedFamilyRowLoad]
    | succ k ih=>
      intro hk
      have hkN:k≤N:=by omega
      obtain ⟨C,hC,hdis,hcap⟩:=ih hkN
      let e:Fin k↪Fin N:=⟨fun j=>⟨j.val,lt_of_lt_of_le j.isLt hkN⟩,by intro a b h;exact Fin.ext (congrArg (fun z:Fin N=>z.val) h)⟩
      let i:Fin N:=⟨k,by omega⟩
      have hr (a:V):markedFamilyRowLoad C a≤K+D₀:=load_bound e C hC hcap a
      let D:=markedFamilyRim C
      let S:=Finset.univ.filter (fun a=>K≤markedFamilyRowLoad C a)
      let Z:=Finset.univ.filter (fun a=>markedFamilySpokes C a (u i))
      have hS:(S.card:ℝ)≤(N*(l+4):ℕ)/(K:ℝ):=by
        apply (le_div_iff₀ (Nat.cast_pos.mpr hK)).mpr
        have hh:K*S.card≤N*(l+4):=(markedFamilyRowLoad_saturated C K).trans
          (by simp only [Fintype.card_fin];exact Nat.mul_le_mul_right (l+4) hkN)
        exact_mod_cast (by simpa only [Nat.mul_comm] using hh)
      have hZ:Z.card≤D₀*(l+4):=(markedFamilySpokes_column C (u i)).trans
        (Nat.mul_le_mul_right (l+4) (hub_bound e C hC (u i)))
      have hW:(((Xᶜ)∪(S∪Z)).card:ℝ)≤((Xᶜ).card:ℝ)+(N*(l+4):ℕ)/(K:ℝ)+(D₀*(l+4):ℕ):=by
        have hh:(((Xᶜ)∪(S∪Z)).card:ℝ)≤(Xᶜ).card+(S.card+Z.card):=by
          exact_mod_cast (Finset.card_union_le _ _).trans (Nat.add_le_add_left (Finset.card_union_le _ _) _)
        have hz:(Z.card:ℝ)≤(D₀*(l+4):ℕ):=by exact_mod_cast hZ
        linarith only [hh,hS,hz]
      have hD:∀ a,(D.degree a:ℝ)≤4*(K+D₀:ℕ):=by
        intro a
        have hh: (D.degree a)≤4*(K+D₀):=(markedFamilyRim_degree hb C a).trans
          (by have h1:=hr a;have h2:=hr (π.symm a);omega)
        exact_mod_cast hh
      have hroot:¬markedFamilySpokes C (x i) (u i):=by
        rintro ⟨j,hju,hjx⟩
        have hxi:x i=x (e j):=by
          rcases (hC j).2.2 (x i) hjx with h|h
          · exact h
          · exact (hx i h).elim
        have hui:u i=u (e j):=hju.symm.trans (hC j).1
        have he:=congrArg (fun z:Fin N=>z.val) (hedge (Prod.ext hxi hui))
        have hj':=j.isLt
        dsimp [i,e] at he
        omega
      obtain ⟨W,hWu,hWx,hWD,hWs⟩:=marked_spoke_wheel_after_deletion Q hl D
        (4*(K+D₀:ℕ)) (by positivity) hD (t i) (x i) (u i) (hH i) ((Xᶜ)∪(S∪Z))
        (by linarith only [hW,hbudget])
      have hWG:Good i W:=⟨hWu,hWx,by
        intro a ha
        rcases hWs a ha with h|h
        · exact Or.inl h
        · exact Or.inr (by by_contra hn;exact h (Finset.mem_union_left _ (Finset.mem_compl.mpr hn)))⟩
      have hcross (j:Fin k):Disjoint (markedWheelPhysicalResources (C j)) (markedWheelPhysicalResources W):=by
        apply Finset.disjoint_left.mpr
        intro z hz hzW
        cases z with
        | inl z=>
          rw [markedWheelPhysicalResources_rim] at hz hzW
          have hc:z.card=2:=by
            obtain ⟨a,_,ha⟩:=Finset.mem_image.mp hz
            rw [←ha]
            exact markedCycle_physical_edge_card tail head ktail khead (l+3) π b (by omega) hb (C j).1 a
          obtain ⟨a,d,had,rfl⟩:=Finset.card_eq_two.mp hc
          exact disjoint_graphs_no_common_edge _ _ hWD a d ⟨had,hzW⟩ (SimpleGraph.iSup_adj.mpr ⟨j,had,hz⟩)
        | inr au=>
          rw [markedWheelPhysicalResources_spoke] at hz hzW
          have he:au.2=u i:=hzW.1.symm.trans hWu
          have hold:markedFamilySpokes C au.1 (u i):=⟨j,hz.1.trans he,hz.2⟩
          rcases hWs au.1 hzW.2 with h|h
          · rw [h] at hold;exact hroot hold
          · exact h (Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hold⟩)))
      refine ⟨Fin.snoc C W,?_,?_,?_⟩
      · intro j
        refine Fin.lastCases ?_ (fun j=>?_) j
        · simpa only [Fin.snoc_last,Fin.val_last,i] using hWG
        · simpa only [Fin.snoc_castSucc,Fin.val_castSucc] using hC j
      · intro j q
        refine Fin.lastCases ?_ (fun j'=>?_) j
        · refine Fin.lastCases ?_ (fun q'=>?_) q
          · intro h;exact (h rfl).elim
          · intro _;simpa only [Fin.snoc_last,Fin.snoc_castSucc] using (hcross q').symm
        · refine Fin.lastCases ?_ (fun q'=>?_) q
          · intro _;simpa only [Fin.snoc_last,Fin.snoc_castSucc] using hcross j'
          · intro h
            simpa only [Fin.snoc_castSucc] using hdis j' q' (fun he=>h (congrArg Fin.castSucc he))
      · intro a ha
        rw [markedFamilyRowLoad_snoc]
        by_cases haw:a∈markedWheelRows W
        · rw [if_pos haw]
          have haS:a∉S:=by
            rcases hWs a haw with h|h
            · exact (hx i (h ▸ ha)).elim
            · exact fun hs=>h (Finset.mem_union_right _ (Finset.mem_union_left _ hs))
          have hh:markedFamilyRowLoad C a<K:=by simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and,not_le] using haS
          omega
        · rw [if_neg haw,Nat.add_zero];exact hcap a ha
  obtain ⟨C,hC,hdis,hcap⟩:=hp N le_rfl
  have hr:∀ a,markedFamilyRowLoad C a≤K+D₀:=load_bound (Function.Embedding.refl _) C hC hcap
  refine ⟨C,hC,hdis,hcap,?_,?_,?_⟩
  · intro a
    apply (markedFamilyRim_degree hb C a).trans
    have h1:=hr a;have h2:=hr (π.symm a);omega
  · intro a;exact (markedFamilySpokes_row C a).trans (hr a)
  · intro v;exact (markedFamilySpokes_column C v).trans
      (Nat.mul_le_mul_right (l+4) (hub_bound (Function.Embedding.refl _) C hC v))

end Oberwolfach
