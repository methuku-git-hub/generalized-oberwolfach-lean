module

public import Oberwolfach.BufferedOrientedSourceComplement
public import Oberwolfach.FactorOrientationReservedBlocks
public import Oberwolfach.LongReservedInteriorPath

@[expose] public section
/-! The actual reserved source blocks induce the required source tail/head
complement identity under the globally chosen cycle orientation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem reserved_factor_orientation_complement
    {X I J:Type*} [Fintype X] [DecidableEq X] [Fintype I] [Fintype J]
    (G:SimpleGraph X) (hG:G.IsRegularOfDegree 2)
    (components:I↪G.ConnectedComponent)
    (e:∀i:I,SimpleGraph.cycleGraph (Fintype.card (components i)) ≃g (components i).toSimpleGraph)
    (c d:ℕ) (hc:0<c) (t:J→ℕ) (ht:∀i,t i≤d) (htpos:∀i,0<t i)
    (index:J↪LongReservedBlockIndex G components c d):
    let n:J→ℕ:=fun i=>c*t i
    let ext:∀i,Fin (n i+5)↪X:=fun i=>longReservedSigmaBlock G components c d e (index i) (t i) (ht i)
    let inner:∀i,Fin (n i+1)↪X:=fun i=>longReservedInteriorEmbedding (n i) (ext i)
    let σ:=factorCycleOrientation G (extendComponentCycleChoices G hG components e)
    ((Finset.univ\bufferedPathFullDomain n inner)∪bufferedFinalEndpoints n inner).image σ=
      (Finset.univ\bufferedPathFullDomain n inner)∪Finset.univ.image (fun i=>inner i 0):=by
  let n:J→ℕ:=fun i=>c*t i
  let ext:∀i,Fin (n i+5)↪X:=fun i=>longReservedSigmaBlock G components c d e (index i) (t i) (ht i)
  let inner:∀i,Fin (n i+1)↪X:=fun i=>longReservedInteriorEmbedding (n i) (ext i)
  let σ:=factorCycleOrientation G (extendComponentCycleChoices G hG components e)
  have hinner:∀i p,inner i p=ext i ⟨p.val+2,by omega⟩:=by intro i p;rfl
  have hdis:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)):=by
    intro i j hij
    exact long_reserved_sigma_blocks_disjoint G components c d e (index i) (index j)
      (t i) (t j) (ht i) (ht j) (fun h=>hij (index.injective h))
  have hn:∀i,0<n i:=fun i=>Nat.mul_pos hc (htpos i)
  have hstep:∀i (p:Fin (n i)),σ (inner i p.castSucc)=inner i p.succ:=by
    intro i p
    have hp:p.val<c*t i:=p.isLt
    have hh:=factor_cycle_orientation_reserved_block_step G hG components e c d (index i) (t i) (ht i)
      ⟨p.val+2,by omega⟩
    change σ (ext i ⟨p.val+2,by omega⟩)=ext i ⟨p.val+1+2,by omega⟩
    simpa only [σ,ext,n,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
  exact buffered_oriented_source_complement n ext inner hinner hdis σ hn hstep
end Oberwolfach
