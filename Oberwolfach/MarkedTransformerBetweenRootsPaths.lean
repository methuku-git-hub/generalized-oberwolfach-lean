module

public import Oberwolfach.SeparatedDirectedPaths

@[expose] public section

/-! Actual shared paths for a marked spoke-edge or vertex-wheel pair.
Both attachments see the two old roots. An internal marked head, if present,
has marked spokes at both hubs; all other free vertices have ordinary spokes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [DecidableEq V]

 theorem marked_transformer_between_roots_path (F:SimpleGraph V)
    (R₀ RK:V→V→Prop) (H₀ HK:V→U→Prop) (v v' w w':V) (u u':U) (j closeMarked:Bool)
    (W Z:Finset V) (l:ℕ) (hl:2≤l)
    (d c:ℝ) (hd:0≤d) (hF:∀ x,(F.degree x:ℝ)≤d)
    (hopen:c≤((Finset.univ.filter (fun a=>R₀ v a∧R₀ v' a∧H₀ a u∧H₀ a u')).card:ℝ))
    (hclose:c≤((Finset.univ.filter (fun a=>(if closeMarked then RK a w∧RK a w' else R₀ a w∧R₀ a w')∧H₀ a u∧H₀ a u')).card:ℝ))
    (hstep:∀ t:Bool,∀ x,c≤((Finset.univ.filter (fun a=>
      (if t then RK x a else R₀ x a)∧(if t then HK a u∧HK a u' else H₀ a u∧H₀ a u'))).card:ℝ))
    (hjoin:∀ x y,x≠y→c≤((Finset.univ.filter (fun a=>R₀ x a∧R₀ a y∧H₀ a u∧H₀ a u')).card:ℝ))
    (hbudget:W.card+((Z.card:ℝ)+l+4)*(d+1)<c):
    ∃ p:Fin (l+3)↪V,
      (R₀ v (p 0)∧R₀ v' (p 0))∧
      (if closeMarked then RK (p (Fin.last (l+2))) w∧RK (p (Fin.last (l+2))) w'
       else R₀ (p (Fin.last (l+2))) w∧R₀ (p (Fin.last (l+2))) w')∧
      (∀ i:Fin (l+2),if j=false∧i.val=1 then RK (p i.castSucc) (p i.succ)
        else R₀ (p i.castSucc) (p i.succ))∧
      (∀ i,if j=false∧i.val=2 then HK (p i) u∧HK (p i) u'
        else H₀ (p i) u∧H₀ (p i) u')∧
      (∀ i,p i∉W∧p i∉Z∧∀ z∈Z,¬F.Adj (p i) z)∧
      ∀ i k,¬F.Adj (p i) (p k):=by
  have haBudget:W.card+(Z.card:ℝ)*(d+1)<c:=by nlinarith only [hbudget,hd,Nat.cast_nonneg (α:=ℝ) l]
  obtain ⟨a,ha,haW,haZ,haF⟩:=candidate_vertex_avoiding F _ W Z d c hF hopen haBudget
  have hins:((insert a Z).card:ℝ)≤Z.card+1:=by exact_mod_cast Finset.card_insert_le a Z
  have hbBudget:W.card+((insert a Z).card:ℝ)*(d+1)<c:=by
    have hh:=mul_le_mul_of_nonneg_right hins (show 0≤d+1 by linarith)
    nlinarith only [hbudget,hh,hd,Nat.cast_nonneg (α:=ℝ) l]
  obtain ⟨z,hz,hzW,hzZ,hzF⟩:=candidate_vertex_avoiding F _ W (insert a Z) d c hF hclose hbBudget
  have hza:z≠a:=fun h=>hzZ (by simp [h])
  have hazF:¬F.Adj a z:=fun h=>hzF a (Finset.mem_insert_self _ _) h.symm
  let D:ℕ→V→V→Prop:=fun i x y=>if j=false∧i=1 then RK x y else R₀ x y
  let A:ℕ→Finset V:=fun i=>Finset.univ.filter (fun x=>if j=false∧i=2 then HK x u∧HK x u' else H₀ x u∧H₀ x u')
  have haA:a∈A 0:=by
    simpa only [A,show (0:ℕ)≠2 by omega,and_false,ite_false,Finset.mem_filter,Finset.mem_univ,true_and] using (Finset.mem_filter.mp ha).2.2.2
  have hzA:z∈A (l+2):=by
    have hn:l+2≠2:=by omega
    simpa only [A,hn,and_false,ite_false,Finset.mem_filter,Finset.mem_univ,true_and] using (Finset.mem_filter.mp hz).2.2
  have hc:∀ i<l,∀ x∈A i,c≤(((A (i+1)).filter (D i x)).card:ℝ):=by
    intro i hi x hx
    have he:(j=false∧i+1=2)↔(j=false∧i=1):=by
      constructor <;> rintro ⟨hj,hi⟩ <;> exact ⟨hj,by omega⟩
    by_cases ht:j=false∧i=1
    · have hset:(A (i+1)).filter (D i x)=Finset.univ.filter (fun a=>RK x a∧(HK a u∧HK a u')):=by
        ext y
        simp only [A,D,Finset.mem_filter,Finset.mem_univ,true_and,he,ht,ite_true]
        tauto
      rw [hset]
      exact hstep true x
    · have hset:(A (i+1)).filter (D i x)=Finset.univ.filter (fun a=>R₀ x a∧(H₀ a u∧H₀ a u')):=by
        ext y
        simp only [A,D,Finset.mem_filter,Finset.mem_univ,true_and,he,ht,ite_false]
        tauto
      rw [hset]
      exact hstep false x
  have hj:∀ x∈A l,x≠z→c≤(((A (l+1)).filter (fun y=>D l x y∧D (l+1) y z)).card:ℝ):=by
    intro x hx hxz
    have h₁:l≠1:=by omega
    have h₂:l+1≠1:=by omega
    have h₃:l+1≠2:=by omega
    have hset:(A (l+1)).filter (fun y=>D l x y∧D (l+1) y z)=
        Finset.univ.filter (fun y=>R₀ x y∧R₀ y z∧H₀ y u∧H₀ y u'):=by
      ext y
      simp only [A,D,h₁,h₂,h₃,and_false,ite_false,Finset.mem_filter,Finset.mem_univ,true_and]
      tauto
    rw [hset]
    exact hjoin x z hxz
  obtain ⟨p,hp0,hplast,hpA,hpD,hpF⟩:=separated_directed_path F D A W Z d c hd hF l a z hza.symm hazF
    haA hzA haW hzW haZ (fun h=>hzZ (Finset.mem_insert_of_mem h)) haF
    (fun w hw=>hzF w (Finset.mem_insert_of_mem hw)) (by intro i hi x hx;simpa only [D] using hc i hi x hx)
    (by intro x hx hxz;simpa only [D] using hj x hx hxz) hbudget
  refine ⟨p,?_,?_,hpD,?_,?_,hpF⟩
  · rw [hp0];exact ⟨(Finset.mem_filter.mp ha).2.1,(Finset.mem_filter.mp ha).2.2.1⟩
  · rw [hplast];exact (Finset.mem_filter.mp hz).2.1
  · intro i;exact (Finset.mem_filter.mp (hpA i).1).2
  · intro i;exact (hpA i).2

end Oberwolfach
