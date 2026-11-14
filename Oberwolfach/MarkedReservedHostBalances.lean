module

public import Oberwolfach.MarkedBalanceReservationEvent
public import Oberwolfach.MarkedBalanceTermDegrees
public import Oberwolfach.MarkedBalanceTermRestriction
public import Oberwolfach.MarkedBalanceReservationErrors

@[expose] public section

/-! The actual complementary typed host satisfies the four numerical
near-balance inequalities. The coefficient m is retained in the hub
identity, and all six degree tests use one original sampling event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U]

theorem markedSixDegreeBalance_row (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (m:ℕ) (v:V):
    let d:=fun j=>((markedBalanceTermSet tail head ktail khead H₀ HK (Sum.inl v) j).card:ℝ);
    markedSixDegreeBalance m d 0=occurrenceDegree (Sum.elim tail ktail) v-
      (∑ u,if H₀ v u then (1:ℝ) else 0)-(∑ u,if HK v u then (1:ℝ) else 0)∧
    markedSixDegreeBalance m d 1=occurrenceDegree (Sum.elim head khead) v-
      (∑ u,if H₀ v u then (1:ℝ) else 0)-(∑ u,if HK v u then (1:ℝ) else 0)∧
    markedSixDegreeBalance m d 2=occurrenceDegree khead v-(∑ u,if HK v u then (1:ℝ) else 0):=by
  intro d
  obtain ⟨h0,h1,h2,h3,h4,h5⟩:=markedBalanceTermSet_row_degrees tail head ktail khead H₀ HK v
  have hd0:d 0=occurrenceDegree tail v:=by convert h0 using 1 <;> congr!
  have hd1:d 1=occurrenceDegree ktail v:=by convert h1 using 1 <;> congr!
  have hd2:d 2=occurrenceDegree head v:=by convert h2 using 1 <;> congr!
  have hd3:d 3=occurrenceDegree khead v:=by convert h3 using 1 <;> congr!
  have hd4:d 4=(∑ u,if H₀ v u then (1:ℝ) else 0):=by convert h4 using 1 <;> congr!
  have hd5:d 5=(∑ u,if HK v u then (1:ℝ) else 0):=by convert h5 using 1 <;> congr!
  refine ⟨?_,?_,?_⟩
  · change d 0+d 1-d 4-d 5=_
    rw [hd0,hd1,hd4,hd5,occurrenceDegree_sum]
  · change d 2+d 3-d 4-d 5=_
    rw [hd2,hd3,hd4,hd5,occurrenceDegree_sum]
  · change d 3-d 5=_
    rw [hd3,hd5]

theorem markedSixDegreeBalance_hub (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (m:ℕ) (u:U):
    markedSixDegreeBalance m (fun j=>((markedBalanceTermSet tail head ktail khead H₀ HK (Sum.inr u) j).card:ℝ)) 3=
      (∑ v,if H₀ v u then (1:ℝ) else 0)-(m:ℝ)*(∑ v,if HK v u then (1:ℝ) else 0):=by
  obtain ⟨h0,h1⟩:=markedBalanceTermSet_hub_degrees tail head ktail khead H₀ HK u
  change _- (m:ℝ)*_=_
  convert congrArg₂ (fun a b:ℝ=>a-(m:ℝ)*b) h0 h1 using 1 <;> congr!

theorem marked_reserved_host_balance_event (ε:ℝ) (hε:0<ε) (q:ℕ):
    ∃ N:ℕ,∀ (V U E K:Type) [Fintype V] [Fintype U] [Fintype E] [Fintype K]
      [DecidableEq V] [DecidableEq U],N≤Fintype.card (V⊕U)→
    ∀ (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (π:Equiv.Perm V),
    Function.Injective (markedPhysicalEdge tail head ktail khead π)→
    ∀ (X:Finset V) (Z:Finset U) (m:ℕ) (η η':ℝ),0≤η→0≤η'→
    let a:=fun r j=>((markedBalanceTermSet tail head ktail khead H₀ HK r j).card:ℝ)
    let c:=fun r j=>(((markedBalanceTermSet tail head ktail khead H₀ HK r j).filter (fun e=>
      (if markedActiveAuxTail tail ktail H₀ HK e=r then markedActiveAuxHead head khead H₀ HK e
        else markedActiveAuxTail tail ktail H₀ HK e)∈ordinaryInnerVertices X Z)).card:ℝ);
    (∀ (v:V) (i:Fin 3),|markedSixDegreeBalance m (a (Sum.inl v)) i.castSucc|≤η)→
    (∀ (v:V) (i:Fin 3),|markedSixDegreeBalance m (c (Sum.inl v)) i.castSucc|≤η')→
    (∀ u,|markedSixDegreeBalance m (a (Sum.inr u)) 3|≤η)→
    (∀ u,|markedSixDegreeBalance m (c (Sum.inr u)) 3|≤η')→
    ∀ (p:ℝ) (hp:0≤p) (hp1:p≤1),
    1-1/(Fintype.card (V⊕U):ℝ)^q≤
      (FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp hp1)).probability
      (fun σ=>
        let PE:=fun e:E=>¬markedBoundaryRimAllowed π X σ false (tail e) (head e)
        let PK:=fun e:K=>¬markedBoundaryRimAllowed π X σ true (ktail e) (khead e)
        let t':=fun e:{e//PE e}=>tail e.val
        let h':=fun e:{e//PE e}=>head e.val
        let kt':=fun e:{e//PK e}=>ktail e.val
        let kh':=fun e:{e//PK e}=>khead e.val
        let H₀':=fun x u=>H₀ x u∧¬markedBoundarySpokeAllowed X Z σ x u
        let HK':=fun x u=>HK x u∧¬markedBoundarySpokeAllowed X Z σ x u
        let δ:=η+η'+(m+4)*ε*Fintype.card (V⊕U);
        (∀ v,|occurrenceDegree (Sum.elim t' kt') v-
          (∑ u,if H₀' v u then (1:ℝ) else 0)-(∑ u,if HK' v u then (1:ℝ) else 0)|≤δ)∧
        (∀ v,|occurrenceDegree (Sum.elim h' kh') v-
          (∑ u,if H₀' v u then (1:ℝ) else 0)-(∑ u,if HK' v u then (1:ℝ) else 0)|≤δ)∧
        (∀ v,|occurrenceDegree kh' v-(∑ u,if HK' v u then (1:ℝ) else 0)|≤δ)∧
        (∀ u,|(∑ v,if H₀' v u then (1:ℝ) else 0)-(m:ℝ)*(∑ v,if HK' v u then (1:ℝ) else 0)|≤δ)):=by
  obtain ⟨N,hN⟩:=marked_balance_reservation_common_event ε hε q
  refine ⟨N,?_⟩
  intro V U E K _ _ _ _ _ _ hn tail head ktail khead H₀ HK π hphys X Z m η η' hη hη' a c ha hc hau hcu p hp hp1
  apply (hN V U E K hn tail head ktail khead H₀ HK π hphys X Z p hp hp1).trans
  apply finiteLaw_probability_mono
  intro σ hσ PE PK t' h' kt' kh' H₀' HK' δ
  let d:=fun r j=>((markedBalanceTermSet t' h' kt' kh' H₀' HK' r j).card:ℝ)
  have hdeg (r:V⊕U) (j:Fin 6):|d r j-(if r∈ordinaryInnerVertices X Z
      then (1-p)*(a r j-c r j) else a r j-p*c r j)|≤ε*Fintype.card (V⊕U):=by
    have he:=markedBalanceTermSet_restriction_card (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
      (H₀:=H₀) (HK:=HK) PE PK (fun x u=>¬markedBoundarySpokeAllowed X Z σ x u) r j
    have he':d r j=((markedBalanceTermSet tail head ktail khead H₀ HK r j).filter
        (markedActiveRetained PE PK H₀' HK')).card:=by
      convert congrArg (fun n:ℕ=>(n:ℝ)) he using 1 <;> congr!
    rw [he']
    convert hσ r j using 1 <;> congr!
  have hbound (r:V⊕U) (i:Fin 4) (h0:|markedSixDegreeBalance m (a r) i|≤η)
      (h1:|markedSixDegreeBalance m (c r) i|≤η'):
      |markedSixDegreeBalance m (d r) i|≤δ:=by
    have he:=marked_reservation_balance_errors m (a r) (c r) (d r) p (ε*Fintype.card (V⊕U)) η η'
      hp hp1 (by positivity) hη hη' (decide (r∈ordinaryInnerVertices X Z))
      (by intro j;simpa only [decide_eq_true_eq] using hdeg r j) i h0 h1
    dsimp only [δ]
    nlinarith only [he]
  have hrow (v:V):=markedSixDegreeBalance_row t' h' kt' kh' H₀' HK' m v
  have hcol (u:U):=markedSixDegreeBalance_hub t' h' kt' kh' H₀' HK' m u
  refine ⟨?_,?_,?_,?_⟩
  · intro v
    apply le_trans (b:=|markedSixDegreeBalance m (d (Sum.inl v)) 0|)
    · apply le_of_eq;congr 1
      convert (hrow v).1.symm using 1 <;> congr!
    · exact hbound (Sum.inl v) 0 (ha v 0) (hc v 0)
  · intro v
    apply le_trans (b:=|markedSixDegreeBalance m (d (Sum.inl v)) 1|)
    · apply le_of_eq;congr 1
      convert (hrow v).2.1.symm using 1 <;> congr!
    · exact hbound (Sum.inl v) 1 (ha v 1) (hc v 1)
  · intro v
    apply le_trans (b:=|markedSixDegreeBalance m (d (Sum.inl v)) 2|)
    · apply le_of_eq;congr 1
      convert (hrow v).2.2.symm using 1 <;> congr!
    · exact hbound (Sum.inl v) 2 (ha v 2) (hc v 2)
  · intro u
    apply le_trans (b:=|markedSixDegreeBalance m (d (Sum.inr u)) 3|)
    · apply le_of_eq;congr 1
      convert (hcol u).symm using 1 <;> congr!
    · exact hbound (Sum.inr u) 3 (hau u) (hcu u)
end Oberwolfach
