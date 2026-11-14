module

public import Oberwolfach.SeparatedDirectedPrefixes

@[expose] public section
/-! For a wheel with five ordinary rim arcs and one marked rim arc, expose
the marked step before the final ordinary two-edge join to a single closing root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [DecidableEq V]

theorem five_wheel_path_to_single_root (F:SimpleGraph V)
    (R₀ RK:V→V→Prop) (H₀ HK:V→U→Prop) (x y:V) (u:U) (j:Bool)
    (W Z:Finset V) (d c:ℝ) (hd:0≤d) (hF:∀ v,(F.degree v:ℝ)≤d)
    (hyZ:y∈Z)
    (hopen:c≤((Finset.univ.filter (fun a=>R₀ x a∧H₀ a u)).card:ℝ))
    (hstep:∀ t:Bool,∀ v,c≤((Finset.univ.filter (fun a=>
      (if t then RK v a else R₀ v a)∧(if t then HK a u else H₀ a u))).card:ℝ))
    (hjoin:∀ v,v≠y→c≤((Finset.univ.filter (fun z=>R₀ v z∧R₀ z y∧H₀ z u)).card:ℝ))
    (hbudget:(W.card:ℝ)+((Z.card:ℝ)+5)*(d+1)<c):
    ∃ p:Fin 4↪V,
      R₀ x (p 0)∧R₀ (p 3) y∧
      (∀ i:Fin 3,if j=false∧i.val=1 then RK (p i.castSucc) (p i.succ)
        else R₀ (p i.castSucc) (p i.succ))∧
      (∀ i,if j=false∧i.val=2 then HK (p i) u else H₀ (p i) u)∧
      (∀ i,p i∉W∧p i∉Z∧∀ z∈Z,¬F.Adj (p i) z)∧
      ∀ i k,¬F.Adj (p i) (p k):=by
  have hstart:(W.card:ℝ)+(Z.card:ℝ)*(d+1)<c:=by nlinarith only [hbudget,hd]
  obtain ⟨a,ha,haW,haZ,haF⟩:=candidate_vertex_avoiding F _ W Z d c hF hopen hstart
  let D:ℕ→V→V→Prop:=fun i v w=>if j=false∧i=1 then RK v w else R₀ v w
  let A:ℕ→Finset V:=fun i=>Finset.univ.filter (fun v=>if j=false∧i=2 then HK v u else H₀ v u)
  letI (i:ℕ) (v z:V):Decidable (D i v z):=Classical.propDecidable _
  have haA:a∈A 0:=by simpa [A] using (Finset.mem_filter.mp ha).2.2
  have hcount:∀ i<2,∀ v∈A i,c≤(((A (i+1)).filter (D i v)).card:ℝ):=by
    intro i hi v hv
    have he:(j=false∧i+1=2)↔(j=false∧i=1):=by constructor <;> rintro ⟨hj,hi⟩ <;> exact ⟨hj,by omega⟩
    by_cases ht:j=false∧i=1
    · have hs:(A (i+1)).filter (D i v)=Finset.univ.filter (fun z=>RK v z∧HK z u):=by
        ext z
        simp only [A,D,Finset.mem_filter,Finset.mem_univ,true_and,he,ht,ite_true]
        tauto
      rw [hs];exact hstep true v
    · have hs:(A (i+1)).filter (D i v)=Finset.univ.filter (fun z=>R₀ v z∧H₀ z u):=by
        ext z
        simp only [A,D,Finset.mem_filter,Finset.mem_univ,true_and,he,ht,ite_false]
        tauto
      rw [hs];exact hstep false v
  have hpBudget:(W.card:ℝ)+((Z.card:ℝ)+2+1)*(d+1)<c:=by nlinarith only [hbudget,hd]
  obtain ⟨p,hp0,hpA,hpD,hpF⟩:=separated_directed_prefix F D A W Z d c hd hF 2 a haA haW haZ haF hcount hpBudget
  let S:Finset V:=Finset.univ.image p
  have hS:S.card=3:=by dsimp only [S];rw [Finset.card_image_of_injective _ p.injective,Finset.card_univ,Fintype.card_fin]
  have hZS:((Z∪S).card:ℝ)≤Z.card+3:=by
    have hh:((Z∪S).card:ℝ)≤Z.card+S.card:=by exact_mod_cast Finset.card_union_le Z S
    rw [hS] at hh
    push_cast at hh
    exact hh
  have hchoice:(W.card:ℝ)+((Z∪S).card:ℝ)*(d+1)<c:=by
    have hh:=mul_le_mul_of_nonneg_right hZS (show 0≤d+1 by linarith)
    nlinarith only [hh,hbudget,hd]
  have hp2ne:p 2≠y:=fun h=>(hpA 2).2.2.1 (h ▸ hyZ)
  obtain ⟨z,hz,hzW,hzZS,hzF⟩:=candidate_vertex_avoiding F
    (Finset.univ.filter (fun z=>R₀ (p 2) z∧R₀ z y∧H₀ z u)) W (Z∪S) d c hF (hjoin (p 2) hp2ne) hchoice
  have hzout:z∉Set.range p:=by
    rintro ⟨i,hi⟩
    exact hzZS (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩))
  let q:Fin 4↪V:=⟨Fin.snoc p z,Fin.snoc_injective_of_injective p.injective hzout⟩
  have hqold (i:Fin 3):q i.castSucc=p i:=by simp only [q,Function.Embedding.coeFn_mk,Fin.snoc_castSucc]
  have hq0:q 0=p 0:=by simpa using hqold 0
  have hq1:q 1=p 1:=by simpa using hqold 1
  have hq2:q 2=p 2:=by simpa using hqold 2
  have hqlast:q (Fin.last 3)=z:=by simp only [q,Function.Embedding.coeFn_mk,Fin.snoc_last]
  have hq3:q 3=z:=by simpa using hqlast
  have hzP: R₀ (p 2) z ∧ R₀ z y ∧ H₀ z u:=(Finset.mem_filter.mp hz).2
  refine ⟨q,?_,?_,?_,?_,?_,?_⟩
  · rw [hq0,hp0];exact (Finset.mem_filter.mp ha).2.1
  · rw [hq3];exact hzP.2.1
  · intro i
    fin_cases i <;> norm_num
    · change R₀ (q 0) (q 1)
      rw [hq0,hq1]
      simpa [D] using hpD 0
    · rw [hq1,hq2]
      cases j <;> simpa [D] using hpD 1
    · change R₀ (q 2) (q 3)
      rw [hq2,hq3];exact hzP.1
  · intro i
    fin_cases i <;> norm_num
    · change H₀ (q 0) u
      rw [hq0];simpa [A] using (hpA 0).1
    · change H₀ (q 1) u
      rw [hq1];simpa [A] using (hpA 1).1
    · rw [hq2]
      cases j <;> simpa [A] using (hpA 2).1
    · change H₀ (q 3) u
      rw [hq3];exact hzP.2.2
  · intro i
    refine Fin.lastCases ?_ (fun t=>?_) i
    · rw [hqlast]
      exact ⟨hzW,fun h=>hzZS (Finset.mem_union_left _ h),fun w hw=>hzF w (Finset.mem_union_left _ hw)⟩
    · rw [hqold];exact (hpA t).2
  · intro i k
    refine Fin.lastCases ?_ (fun i=>?_) i
    · rw [hqlast]
      refine Fin.lastCases ?_ (fun k=>?_) k
      · rw [hqlast];exact F.loopless.irrefl _
      · rw [hqold];exact hzF _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩))
    · rw [hqold]
      refine Fin.lastCases ?_ (fun k=>?_) k
      · rw [hqlast];exact fun h=>hzF _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)) h.symm
      · rw [hqold];exact hpF i k
end Oberwolfach
