module

public import Oberwolfach.SeparatedDirectedPaths

@[expose] public section

/-! A marked path with already assigned attachment vertices. Its endpoints
are retained, and only its internal vertices are selected. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [DecidableEq V]

 theorem marked_path_between_attachments (F:SimpleGraph V)
    (R₀ RK:V→V→Prop) (H₀ HK:V→U→Prop) (u u':U) (j:Bool)
    (W Z:Finset V) (l:ℕ) (hl:2≤l) (a z:V)
    (haz:a≠z) (hazF:¬F.Adj a z)
    (haW:a∉W) (hzW:z∉W) (haZ:a∉Z) (hzZ:z∉Z)
    (haF:∀ x∈Z,¬F.Adj a x) (hzF:∀ x∈Z,¬F.Adj z x)
    (haH:H₀ a u∧H₀ a u') (hzH:H₀ z u∧H₀ z u')
    (d c:ℝ) (hd:0≤d) (hF:∀ x,(F.degree x:ℝ)≤d)
    (hstep:∀ t:Bool,∀ x,c≤((Finset.univ.filter (fun y=>
      (if t then RK x y else R₀ x y)∧(if t then HK y u∧HK y u' else H₀ y u∧H₀ y u'))).card:ℝ))
    (hjoin:∀ x y,x≠y→c≤((Finset.univ.filter (fun a=>R₀ x a∧R₀ a y∧H₀ a u∧H₀ a u')).card:ℝ))
    (hbudget:W.card+((Z.card:ℝ)+l+4)*(d+1)<c):
    ∃ p:Fin (l+3)↪V,p 0=a∧p (Fin.last (l+2))=z∧
      (∀ i:Fin (l+2),if j=false∧i.val=1 then RK (p i.castSucc) (p i.succ)
        else R₀ (p i.castSucc) (p i.succ))∧
      (∀ i,if j=false∧i.val=2 then HK (p i) u∧HK (p i) u'
        else H₀ (p i) u∧H₀ (p i) u')∧
      (∀ i,p i∉W∧p i∉Z∧∀ x∈Z,¬F.Adj (p i) x)∧
      ∀ i k,¬F.Adj (p i) (p k):=by
  let D:ℕ→V→V→Prop:=fun i x y=>if j=false∧i=1 then RK x y else R₀ x y
  let A:ℕ→Finset V:=fun i=>Finset.univ.filter (fun x=>if j=false∧i=2 then HK x u∧HK x u' else H₀ x u∧H₀ x u')
  have haA:a∈A 0:=by
    simpa only [A,show (0:ℕ)≠2 by omega,and_false,ite_false,Finset.mem_filter,Finset.mem_univ,true_and] using haH
  have hzA:z∈A (l+2):=by
    have hn:l+2≠2:=by omega
    simpa only [A,hn,and_false,ite_false,Finset.mem_filter,Finset.mem_univ,true_and] using hzH
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
  obtain ⟨p,hp0,hplast,hpA,hpD,hpF⟩:=separated_directed_path F D A W Z d c hd hF l a z haz hazF
    haA hzA haW hzW haZ hzZ haF hzF
    (by intro i hi x hx;simpa only [D] using hc i hi x hx)
    (by intro x hx hxz;simpa only [D] using hj x hx hxz) hbudget
  exact ⟨p,hp0,hplast,hpD,fun i=>(Finset.mem_filter.mp (hpA i).1).2,fun i=>(hpA i).2,hpF⟩

end Oberwolfach
