module

public import Oberwolfach.MarkedEndpointLabelIdentities
public import Oberwolfach.MarkedEndpointIndexEstimates

@[expose] public section

/-! Class sizes and the marked-outgoing/ordinary-spoke gap follow from
single-arc and single-spoke estimates, with the original parent degrees.
The permutation-invariant row domain is fixed and all roots are ambient. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
set_option maxRecDepth 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_endpoint_class_sizes
    (P:SimpleGraph V) (π:Equiv.Perm V) (d h:ℕ) (hh:3≤h) (A:Finset V) (B:Finset U)
    (hA:∀ x,π x∈A↔x∈A) (n:ℕ) (omega t rho:ℝ)
    (ho:0<omega) (ht:0<t) (hrho:0<rho) (hrho1:rho≤1)
    (c:ℕ) (hc:4≤c) (hst:((c:ℝ)-1)*t≤1)
    (hBn:omega*n≤(B.card:ℝ))
    (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color)
    (hq:∀ u∈B,q u g=t) (hs:∀ u∈B,s u j=((c:ℝ)-1)*t)
    (errR errI deltaP eta:ℝ) (hR:0≤errR) (hI:0≤errI) (hP:0≤deltaP)
    (hparent:∀ x,|((P.neighborFinset x∩A).card:ℝ)-2*B.card/rho|≤deltaP)
    (hsmallR:errR+(6*(d:ℝ)+1)+deltaP≤t*omega*n/4)
    (hsmallI:errI≤t*omega*n/4) (heta:eta≤t*omega/8)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hr:MarkedRowsWithSpokes P π d h A (rho*(((c:ℝ)-1)*t)/2) (rho*t/2)
      q s g j errR σ H)
    (hi:MarkedIndicesWithSpokes π d h B q s g j errI σ H):
    (∀ mark incoming x,(t*omega/2)*n≤
      ((markedEndpointLabels P π d A (mark,incoming,x) σ).card:ℝ)) ∧
    (∀ r x,(t*omega/2)*n≤((B.filter (H r x)).card:ℝ)) ∧
    (∀ x,((markedEndpointLabels P π d A (true,false,x) σ).card:ℝ)+2*(eta*n)≤
      (B.filter (H false x)).card):=by
  let w:Bool→ℝ:=fun r=>if r then t else ((c:ℝ)-1)*t
  have hc':(4:ℝ)≤c:=by exact_mod_cast hc
  have hst0:0≤((c:ℝ)-1)*t:=mul_nonneg (by linarith) ht.le
  have htle:t≤1:=by nlinarith only [hst,hc',ht]
  have hw:∀ r,0≤w r∧w r≤1:=by
    intro r;cases r <;> simp only [w,Bool.false_eq_true,ite_false,ite_true]
    · exact ⟨hst0,hst⟩
    · exact ⟨ht.le,htle⟩
  have hwlow:∀ r,t≤w r:=by
    intro r;cases r <;> simp only [w,Bool.false_eq_true,ite_false,ite_true]
    · nlinarith only [hc',ht]
    · exact le_rfl
  have hq':∀ u∈B,q u g=w true:=hq
  have hs':∀ u∈B,s u j=w false:=hs
  have hnum0:(0:ℝ)≤n:=Nat.cast_nonneg n
  have hrim (mark incoming:Bool) (x:V):
      |((markedEndpointLabels P π d A (mark,incoming,x) σ).card:ℝ)-w mark*B.card|
        ≤t*omega*n/4:=by
    have hcol:=marked_endpoint_column_estimates P π d h (by omega) A B
      (rho*(((c:ℝ)-1)*t)/2) (rho*t/2) q s g j errR hR σ H hr w hq' hs' hw (mark,incoming,x)
    have hprob0:0≤rho*w mark/2:=by positivity
    have hprob1:rho*w mark/2≤1:=by
      have hm:=mul_le_mul hrho1 (hw mark).2 (hw mark).1 (by norm_num : (0:ℝ)≤1)
      nlinarith only [hm]
    have hcount:|((markedEndpointLabels P π d A (mark,incoming,x) σ).card:ℝ)-
        (rho*w mark/2)*(markedRowDomain P π (3*d) A {(mark,incoming,x)} ∅).card|≤errR:=by
      convert hcol.1 using 1
      cases mark <;> rfl
    have he:=marked_endpoint_labels_parent_error P π d A hA mark incoming x σ
      (rho*w mark/2) errR (2*B.card/rho) deltaP hprob0 hprob1 hcount (hparent _)
    have hcanc:(rho*w mark/2)*(2*B.card/rho)=w mark*B.card:=by
      calc
        _=(rho/rho)*(w mark*B.card):=by ring
        _=_:=by rw [div_self (ne_of_gt hrho),one_mul]
    rw [hcanc] at he
    have herr:errR+(6*(d:ℝ)+1)+(rho*w mark/2)*deltaP≤t*omega*n/4:=by
      have hm:=mul_le_mul_of_nonneg_right hprob1 hP
      linarith only [hm,hsmallR]
    exact he.trans herr
  have hspoke (r:Bool) (x:V):
      |((B.filter (H r x)).card:ℝ)-w r*B.card|≤t*omega*n/4:=
    (marked_endpoint_index_estimates π d h hh B q s g j errI hI σ H hi w hq' hs' hw r false x).1.trans hsmallI
  have htBn:t*omega*n≤t*B.card:=by
    convert mul_le_mul_of_nonneg_left hBn ht.le using 1 <;> ring
  have hwt (r:Bool):t*B.card≤w r*B.card:=mul_le_mul_of_nonneg_right (hwlow r) (Nat.cast_nonneg _)
  refine ⟨?_,?_,?_⟩
  · intro mark incoming x
    have hb:=(abs_le.mp (hrim mark incoming x)).1
    have hw':=hwt mark
    have hp:0≤t*omega*n:=by positivity
    nlinarith only [hb,hw',htBn,hp]
  · intro r x
    have hb:=(abs_le.mp (hspoke r x)).1
    have hw':=hwt r
    have hp:0≤t*omega*n:=by positivity
    nlinarith only [hb,hw',htBn,hp]
  · intro x
    have hL:=(abs_le.mp (hrim true false x)).2
    have hY:=(abs_le.mp (hspoke false x)).1
    dsimp [w] at hL hY
    have hcg:3*(t*B.card)≤((c:ℝ)-1)*t*B.card:=by
      have hp:0≤t*B.card:=mul_nonneg ht.le (Nat.cast_nonneg _)
      nlinarith only [mul_nonneg (show 0≤(c:ℝ)-4 by linarith) hp]
    have hetan:=mul_le_mul_of_nonneg_right heta hnum0
    have hp:0≤t*omega*n:=by positivity
    nlinarith only [hL,hY,hcg,hetan,htBn,hp]

end Oberwolfach
