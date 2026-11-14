module

public import Oberwolfach.MarkedReferenceLevelChain

@[expose] public section
/-! A finite family of level records suffices for the existing iteration.
Records beyond the last used level are copies of the last one; no estimates
on the empty tail of the vortex are required. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Gamma Color:Type} [Fintype Gamma] [Fintype Color]
variable {r d N NI Kgeom:ℕ}
variable {gamma rho omega t p0 betaA aLoA BA kappa ξ thetaDeep alphaInner omegaInner
  iota β aLo B η x omegaI hIcut deltaI etaBal:ℝ}

variable {count:ℕ} (hc:0<count)
variable (R:Fin count → MarkedReferenceLevelData Gamma Color r d N NI Kgeom gamma rho omega t p0 betaA aLoA BA
      kappa ξ thetaDeep alphaInner omegaInner iota β aLo B η x omegaI hIcut deltaI etaBal)

def markedReferenceClip (i:ℕ):Fin count:=⟨min i (count-1),by omega⟩

theorem markedReferenceClip_next (i:ℕ) (hi:i+1<count):
    (markedReferenceClip hc (i+1)).val=(markedReferenceClip hc i).val+1:=by
  simp only [markedReferenceClip,Nat.min_eq_left (by omega:i≤count-1),
    Nat.min_eq_left (by omega:i+1≤count-1)]

def markedFiniteLevels (i:ℕ):=R (markedReferenceClip hc i)

theorem markedFiniteLevels_prefix {i:ℕ} (hi:i<count):
    markedFiniteLevels hc R i=R ⟨i,hi⟩:=by
  apply congrArg R
  apply Fin.ext
  simp only [markedReferenceClip,Nat.min_eq_left (by omega:i≤count-1)]

theorem markedFiniteLevels_tail {i:ℕ} (hi : count ≤ i):
    markedFiniteLevels hc R i=R ⟨count-1,by omega⟩:=by
  apply congrArg R
  apply Fin.ext
  simp only [markedReferenceClip,Nat.min_eq_right (by omega : count - 1 ≤ i)]

variable [hVP:∀ i,Fintype (R i).VP] [hUP:∀ i,Fintype (R i).UP]
  [hOrder:∀ i,LinearOrder (R i).VP] [hEq:∀ i,DecidableEq (R i).UP]

structure MarkedFiniteReferenceChain where
  nextV : ∀ (i j:Fin count),j.val=i.val+1 → (R j).VP ↪o (R i).VP
  nextU : ∀ (i j:Fin count),j.val=i.val+1 → (R j).UP ↪ (R i).UP
  intoV : ∀ i:Fin count,(R i).VP ↪o (R (markedReferenceClip hc 0)).VP
  intoU : ∀ i:Fin count,(R i).UP ↪ (R (markedReferenceClip hc 0)).UP
  nextComm : ∀ i j h v,nextV i j h ((R j).πP v)=(R i).πP (nextV i j h v)
  ambientComm : ∀ i v,intoV i ((R i).πP v)=(R (markedReferenceClip hc 0)).πP (intoV i v)
  nextVimage : ∀ i j h,Finset.univ.image (nextV i j h)=(R i).I
  nextUimage : ∀ i j h,Finset.univ.image (nextU i j h)=(R i).J
  nextVdeeper : ∀ i j h v,nextV i j h v∈(R i).T ↔ v∈(R j).I
  nextUdeeper : ∀ i j h u,nextU i j h u∈(R i).Wrem ↔ u∈(R j).J
  nextGraph : ∀ i j h,(R j).PP=(R i).PP.comap (nextV i j h)
  nextOutcome : ∀ i j h,(R j).σBase=rawMarkedRestrictPair (nextV i j h) (nextU i j h) (R i).σBase
  nextSpokes : ∀ i j h,(R j).HBase=fun b v u=>(R i).HBase b (nextV i j h v) (nextU i j h u)
  ambientGraph : ∀ i,(R i).PP=(R (markedReferenceClip hc 0)).PP.comap (intoV i)
  ambientOutcome : ∀ i,(R i).σBase=rawMarkedRestrictPair (intoV i) (intoU i) (R (markedReferenceClip hc 0)).σBase
  ambientSpokes : ∀ i,(R i).HBase=fun b v u=>(R (markedReferenceClip hc 0)).HBase b (intoV i v) (intoU i u)
  composeV : ∀ i j h v,intoV j v=intoV i (nextV i j h v)
  composeU : ∀ i j h u,intoU j u=intoU i (nextU i j h u)
  firstV : ∀ v,intoV (markedReferenceClip hc 0) v=v
  firstU : ∀ u,intoU (markedReferenceClip hc 0) u=u

noncomputable def markedFiniteReferenceChainToChain
    (C:MarkedFiniteReferenceChain hc R) :
    letI : ∀ i,Fintype (markedFiniteLevels hc R i).VP:=fun i=>hVP (markedReferenceClip hc i)
    letI : ∀ i,Fintype (markedFiniteLevels hc R i).UP:=fun i=>hUP (markedReferenceClip hc i)
    letI : ∀ i,LinearOrder (markedFiniteLevels hc R i).VP:=fun i=>hOrder (markedReferenceClip hc i)
    letI : ∀ i,DecidableEq (markedFiniteLevels hc R i).UP:=fun i=>hEq (markedReferenceClip hc i)
    MarkedReferenceLevelChain (markedFiniteLevels hc R) count := by
  letI : ∀ i,Fintype (markedFiniteLevels hc R i).VP:=fun i=>hVP (markedReferenceClip hc i)
  letI : ∀ i,Fintype (markedFiniteLevels hc R i).UP:=fun i=>hUP (markedReferenceClip hc i)
  letI : ∀ i,LinearOrder (markedFiniteLevels hc R i).VP:=fun i=>hOrder (markedReferenceClip hc i)
  letI : ∀ i,DecidableEq (markedFiniteLevels hc R i).UP:=fun i=>hEq (markedReferenceClip hc i)
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i hi;exact C.nextV (markedReferenceClip hc i) (markedReferenceClip hc (i+1)) (markedReferenceClip_next hc i hi)
  · intro i hi;exact C.nextU (markedReferenceClip hc i) (markedReferenceClip hc (i+1)) (markedReferenceClip_next hc i hi)
  · intro i;exact C.intoV (markedReferenceClip hc i)
  · intro i;exact C.intoU (markedReferenceClip hc i)
  · intro i hi;exact C.nextComm (markedReferenceClip hc i) (markedReferenceClip hc (i+1)) (markedReferenceClip_next hc i hi)
  · intro i hi;exact C.ambientComm (markedReferenceClip hc i)
  · intro i hi;exact C.nextVimage (markedReferenceClip hc i) (markedReferenceClip hc (i+1)) (markedReferenceClip_next hc i hi)
  · intro i hi;exact C.nextUimage (markedReferenceClip hc i) (markedReferenceClip hc (i+1)) (markedReferenceClip_next hc i hi)
  · intro i hi;exact C.nextVdeeper (markedReferenceClip hc i) (markedReferenceClip hc (i+1)) (markedReferenceClip_next hc i hi)
  · intro i hi;exact C.nextUdeeper (markedReferenceClip hc i) (markedReferenceClip hc (i+1)) (markedReferenceClip_next hc i hi)
  · intro i hi;exact C.nextGraph (markedReferenceClip hc i) (markedReferenceClip hc (i+1)) (markedReferenceClip_next hc i hi)
  · intro i hi;exact C.nextOutcome (markedReferenceClip hc i) (markedReferenceClip hc (i+1)) (markedReferenceClip_next hc i hi)
  · intro i hi;exact C.nextSpokes (markedReferenceClip hc i) (markedReferenceClip hc (i+1)) (markedReferenceClip_next hc i hi)
  · intro i hi;exact C.ambientGraph (markedReferenceClip hc i)
  · intro i hi;exact C.ambientOutcome (markedReferenceClip hc i)
  · intro i hi;exact C.ambientSpokes (markedReferenceClip hc i)
  · intro i hi;exact C.composeV (markedReferenceClip hc i) (markedReferenceClip hc (i+1)) (markedReferenceClip_next hc i hi)
  · intro i hi;exact C.composeU (markedReferenceClip hc i) (markedReferenceClip hc (i+1)) (markedReferenceClip_next hc i hi)
  · exact C.firstV
  · exact C.firstU

end Oberwolfach
