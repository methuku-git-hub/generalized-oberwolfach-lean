module

public import Oberwolfach.WheelLoadBounds
public import Oberwolfach.PrescribedSpokeDeletion

@[expose] public section

/-! Degree-controlled wheel completion of prescribed spokes. The rim
root of each prescribed spoke lies outside X; all other rim vertices lie
in X. Repeated prescribed hubs are allowed with bounded multiplicity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem prescribed_spoke_wheel_packing (Q F:SimpleGraph V) (H:V→U→Prop)
    (X:Finset V) (N r K D₀:ℕ) (hr:3≤r) (hK:0<K)
    (x:Fin N→V) (u:Fin N→U) (hx:∀ i,x i∉X) (hH:∀ i,H (x i) (u i))
    (hedge:Function.Injective (fun i=>(x i,u i)))
    (hend:∀ a,(Finset.univ.filter (fun i=>a=x i)).card≤D₀)
    (hhub:∀ v,(Finset.univ.filter (fun i=>u i=v)).card≤D₀)
    (L b:ℝ) (hL:0≤L) (hF:∀ a,(F.degree a:ℝ)≤L)
    (hcount:∀ i,∀ a c,b≤(((X.filter (fun v=>H v (u i)))∩Q.neighborFinset a∩Q.neighborFinset c).card:ℝ))
    (hbudget:(N*r:ℕ)/(K:ℝ)+(D₀*r:ℕ)+((r:ℝ)+2)*(L+1)+4*(K+D₀:ℕ)<b) :
    ∃ C:Fin N→OrdinaryWheel Q F H r,
      (∀ i,ordinaryWheelHub (C i)=u i ∧ x i∈(ordinaryWheelRim (C i)).support ∧
        ∀ a∈(ordinaryWheelRim (C i)).support,a=x i∨a∈X) ∧
      (∀ i j,i≠j → Disjoint (ordinaryWheelResources (C i)) (ordinaryWheelResources (C j))) ∧
      (∀ a∈X,wheelRimLoad C a≤K) ∧
      (∀ a,(wheelFamilyRim C).degree a≤2*(K+D₀)) ∧
      (∀ a,(Finset.univ.filter (fun v=>wheelFamilySpokes C a v)).card≤K+D₀) ∧
      (∀ v,(Finset.univ.filter (fun a=>wheelFamilySpokes C a v)).card≤D₀*r) :=by
  let Good (i:Fin N) (C:OrdinaryWheel Q F H r):=
    ordinaryWheelHub C=u i ∧ x i∈(ordinaryWheelRim C).support ∧
      ∀ a∈(ordinaryWheelRim C).support,a=x i∨a∈X
  have load_bound {k:ℕ} (e:Fin k↪Fin N) (C:Fin k→OrdinaryWheel Q F H r)
      (hC:∀ j,Good (e j) (C j)) (hcap:∀ a∈X,wheelRimLoad C a≤K) (a:V):wheelRimLoad C a≤K+D₀:=by
    by_cases ha:a∈X
    · exact (hcap a ha).trans (Nat.le_add_right _ _)
    · have hh:wheelRimLoad C a≤(Finset.univ.filter (fun i=>a=x i)).card:=by
        apply Finset.card_le_card_of_injOn e
        · intro j hj
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
          rcases (hC j).2.2 a (Finset.mem_filter.mp hj).2 with h|h
          · exact h
          · exact (ha h).elim
        · intro i _ j _ hij;exact e.injective hij
      exact (hh.trans (hend a)).trans (Nat.le_add_left _ _)
  have hub_bound {k:ℕ} (e:Fin k↪Fin N) (C:Fin k→OrdinaryWheel Q F H r)
      (hC:∀ j,Good (e j) (C j)) (v:U):wheelHubLoad C v≤D₀:=by
    apply le_trans _ (hhub v)
    apply Finset.card_le_card_of_injOn e
    · intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hC j).1.symm.trans (Finset.mem_filter.mp hj).2⟩
    · intro i _ j _ hij;exact e.injective hij
  have hp:∀ k:ℕ,∀ hk:k≤N,∃ C:Fin k→OrdinaryWheel Q F H r,
      (∀ j,Good ⟨j.val,lt_of_lt_of_le j.isLt hk⟩ (C j)) ∧
      (∀ i j,i≠j → Disjoint (ordinaryWheelResources (C i)) (ordinaryWheelResources (C j))) ∧
      ∀ a∈X,wheelRimLoad C a≤K:=by
    intro k
    induction k with
    | zero =>
      intro hk
      refine ⟨Fin.elim0,fun j=>Fin.elim0 j,fun i=>Fin.elim0 i,?_⟩
      intro a _;simp [wheelRimLoad]
    | succ k ih =>
      intro hk
      have hkN:k≤N:=by omega
      obtain ⟨C,hC,hdis,hcap⟩:=ih hkN
      let e:Fin k↪Fin N:=⟨fun j=>⟨j.val,lt_of_lt_of_le j.isLt hkN⟩,by intro a b h;exact Fin.ext (congrArg (fun z:Fin N=>z.val) h)⟩
      let i:Fin N:=⟨k,by omega⟩
      have hl (a:V):wheelRimLoad C a≤K+D₀:=load_bound e C hC hcap a
      let D:=wheelFamilyRim C
      let S:=Finset.univ.filter (fun a=>K≤wheelRimLoad C a)
      let Z:=Finset.univ.filter (fun a=>wheelFamilySpokes C a (u i))
      have hS:(S.card:ℝ)≤(N*r:ℕ)/(K:ℝ):=by
        apply (le_div_iff₀ (Nat.cast_pos.mpr hK)).mpr
        have hh:K*S.card≤N*r:=(wheelRimLoad_saturated C K).trans (by simp only [Fintype.card_fin];exact Nat.mul_le_mul_right r hkN)
        exact_mod_cast (by simpa only [Nat.mul_comm] using hh)
      have hZ:Z.card≤D₀*r:=(wheelHubLoad_spoke_column C (u i)).trans (Nat.mul_le_mul_right r (hub_bound e C hC (u i)))
      have hW:((S∪Z).card:ℝ)≤(N*r:ℕ)/(K:ℝ)+(D₀*r:ℕ):=by
        have hh:((S∪Z).card:ℝ)≤S.card+Z.card:=by exact_mod_cast Finset.card_union_le S Z
        have hz:(Z.card:ℝ)≤(D₀*r:ℕ):=by exact_mod_cast hZ
        linarith only [hh,hS,hz]
      have hD:∀ a,(D.degree a:ℝ)≤2*(K+D₀:ℕ):=by
        intro a
        exact_mod_cast (wheelRimLoad_degree C a).trans (Nat.mul_le_mul_left 2 (hl a))
      have hroot:¬wheelFamilySpokes C (x i) (u i):=by
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
      obtain ⟨W,hWu,hWx,hWD,hWs⟩:=ordinary_spoke_wheel_after_deletion Q D F H
        (X.filter (fun a=>H a (u i))) (S∪Z) (x i) (u i) (hH i)
        (by intro a ha;exact (Finset.mem_filter.mp ha).2) r hr L (2*(K+D₀:ℕ)) b hL hF hD
        (hcount i) (by linarith only [hW,hbudget])
      have hWG:Good i W:=⟨hWu,hWx,by
        intro a ha
        rcases hWs a ha with h|h
        · exact Or.inl h
        · exact Or.inr (Finset.mem_filter.mp h.1).1⟩
      have hcross (j:Fin k):Disjoint (ordinaryWheelResources (C j)) (ordinaryWheelResources W):=by
        apply Finset.disjoint_left.mpr
        intro z hz hzW
        cases z with
        | inl z =>
          rw [ordinaryWheelResources_rim] at hz hzW
          induction z using Sym2.inductionOn with
          | _ a c =>
            exact disjoint_graphs_no_common_edge _ _ hWD a c hzW (SimpleGraph.iSup_adj.mpr ⟨j,hz⟩)
        | inr au =>
          rw [ordinaryWheelResources_spoke] at hz hzW
          have he:au.2=u i:=hzW.1.symm.trans hWu
          have hold:wheelFamilySpokes C au.1 (u i):=⟨j,hz.1.trans he,hz.2⟩
          rcases hWs au.1 hzW.2 with h|h
          · rw [h] at hold;exact hroot hold
          · exact h.2 (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hold⟩))
      refine ⟨Fin.snoc C W,?_,?_,?_⟩
      · intro j
        refine Fin.lastCases ?_ (fun j=>?_) j
        · simpa only [Fin.snoc_last,Fin.val_last,i] using hWG
        · simpa only [Fin.snoc_castSucc,Fin.val_castSucc] using hC j
      · intro j l
        refine Fin.lastCases ?_ (fun j'=>?_) j
        · refine Fin.lastCases ?_ (fun l'=>?_) l
          · intro h;exact (h rfl).elim
          · intro _;simpa only [Fin.snoc_last,Fin.snoc_castSucc] using (hcross l').symm
        · refine Fin.lastCases ?_ (fun l'=>?_) l
          · intro _;simpa only [Fin.snoc_last,Fin.snoc_castSucc] using hcross j'
          · intro h
            simpa only [Fin.snoc_castSucc] using hdis j' l' (fun he=>h (congrArg Fin.castSucc he))
      · intro a ha
        rw [wheelRimLoad_snoc]
        by_cases haw:a∈(ordinaryWheelRim W).support
        · rw [if_pos haw]
          have haS:a∉S:=by
            rcases hWs a haw with h|h
            · exact (hx i (h ▸ ha)).elim
            · exact fun hs=>h.2 (Finset.mem_union_left _ hs)
          have hh:wheelRimLoad C a<K:=by simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and,not_le] using haS
          omega
        · rw [if_neg haw,Nat.add_zero];exact hcap a ha
  obtain ⟨C,hC,hdis,hcap⟩:=hp N le_rfl
  have hl:∀ a,wheelRimLoad C a≤K+D₀:=load_bound (Function.Embedding.refl _) C hC hcap
  refine ⟨C,hC,hdis,hcap,?_,?_,?_⟩
  · intro a;exact (wheelRimLoad_degree C a).trans (Nat.mul_le_mul_left 2 (hl a))
  · intro a;exact (wheelRimLoad_spoke_row C a).trans (hl a)
  · intro v;exact (wheelHubLoad_spoke_column C v).trans (Nat.mul_le_mul_right r (hub_bound (Function.Embedding.refl _) C hC v))

end Oberwolfach
