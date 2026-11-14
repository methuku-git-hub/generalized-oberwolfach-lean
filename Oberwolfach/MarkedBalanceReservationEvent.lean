module

public import Oberwolfach.MarkedBalanceTestSets
public import Oberwolfach.IncidentReservationCountEvent

@[expose] public section

/-! Simultaneous estimates for the actual ordinary outdegree, marked
outdegree, ordinary indegree, marked indegree and the two spoke degrees
following boundary reservation. The original physical coin law is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_balance_reservation_common_event (ε:ℝ) (hε:0<ε) (q:ℕ):
    ∃ N:ℕ,∀ (V U E K:Type) [Fintype V] [Fintype U] [Fintype E] [Fintype K]
      [DecidableEq V] [DecidableEq U],N≤Fintype.card (V⊕U)→
    ∀ (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (π:Equiv.Perm V),
    Function.Injective (markedPhysicalEdge tail head ktail khead π)→
    ∀ (X:Finset V) (Z:Finset U) (p:ℝ) (hp:0≤p) (hp1:p≤1),
    1-1/(Fintype.card (V⊕U):ℝ)^q≤
      (FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp hp1)).probability
      (fun σ=>∀ (r:V⊕U) (j:Fin 6),
        let A:=markedBalanceTermSet tail head ktail khead H₀ HK r j
        let I:=A.filter (fun a=>(if markedActiveAuxTail tail ktail H₀ HK a=r
          then markedActiveAuxHead head khead H₀ HK a else markedActiveAuxTail tail ktail H₀ HK a)∈ordinaryInnerVertices X Z)
        let keep:=markedActiveRetained
          (fun e=>¬markedBoundaryRimAllowed π X σ false (tail e) (head e))
          (fun e=>¬markedBoundaryRimAllowed π X σ true (ktail e) (khead e))
          (fun x u=>H₀ x u∧¬markedBoundarySpokeAllowed X Z σ x u)
          (fun x u=>HK x u∧¬markedBoundarySpokeAllowed X Z σ x u);
        |((A.filter keep).card:ℝ)-
          (if r∈ordinaryInnerVertices X Z then (1-p)*(A.card-I.card) else A.card-p*I.card)|≤ε*Fintype.card (V⊕U)):=by
  obtain ⟨N,hN⟩:=incident_reservation_count_common_event 6 4 ε (by norm_num) hε 1 q
  refine ⟨N,?_⟩
  intro V U E K _ _ _ _ _ _ hn tail head ktail khead H₀ HK π hphys X Z p hp hp1
  classical
  let coin:MarkedActiveEdge E K H₀ HK↪Sym2 (V⊕U):=
    ⟨markedActivePhysicalCoin tail head ktail khead π H₀ HK,
      markedActivePhysicalCoin_injective tail head ktail khead π H₀ HK hphys⟩
  let T:(V⊕U)×Fin 6→Finset (MarkedActiveEdge E K H₀ HK):=
    fun z=>markedBalanceTermSet tail head ktail khead H₀ HK z.1 z.2
  have hcount:(Fintype.card ((V⊕U)×Fin 6):ℝ)≤6*(Fintype.card (V⊕U):ℝ)^1:=by
    simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat,pow_one];nlinarith
  have hT (z:(V⊕U)×Fin 6) (a:MarkedActiveEdge E K H₀ HK) (ha:a∈T z):
      markedActiveAuxTail tail ktail H₀ HK a=z.1∨markedActiveAuxHead head khead H₀ HK a=z.1:=
    markedBalanceTermSet_incident tail head ktail khead H₀ HK z.1 z.2 a ha
  have hsize (z:(V⊕U)×Fin 6):((T z).card:ℝ)≤4*Fintype.card (V⊕U):=by
    exact_mod_cast markedBalanceTermSet_card tail head ktail khead H₀ HK π hphys z.1 z.2
  have hevent:=hN (Fintype.card (V⊕U)) hn (MarkedActiveEdge E K H₀ HK) (V⊕U) (Sym2 (V⊕U))
    ((V⊕U)×Fin 6) hcount (markedActiveAuxTail tail ktail H₀ HK) (markedActiveAuxHead head khead H₀ HK)
    coin (ordinaryInnerVertices X Z) Prod.fst T hT hsize p hp hp1
  apply hevent.trans
  apply finiteLaw_probability_mono
  intro σ hσ r j A I keep
  have he:A.filter keep=(T (r,j)).filter (fun a=>¬((markedActiveAuxTail tail ktail H₀ HK a∈ordinaryInnerVertices X Z∧
      markedActiveAuxHead head khead H₀ HK a∈ordinaryInnerVertices X Z)∨
      ((markedActiveAuxTail tail ktail H₀ HK a∈ordinaryInnerVertices X Z∨
        markedActiveAuxHead head khead H₀ HK a∈ordinaryInnerVertices X Z)∧σ (coin a)=true))):=by
    ext a
    simp only [Finset.mem_filter]
    exact and_congr_right (fun _=>marked_active_reservation_complement tail head ktail khead H₀ HK π X Z σ a)
  rw [he]
  convert hσ (r,j) using 1 <;> congr!
end Oberwolfach
