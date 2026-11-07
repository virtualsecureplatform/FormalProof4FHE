module
import all FormalProof4FHE.HasteBoots.ConcreteNTTU256Division
import all FormalProof4FHE.HasteBoots.ConcreteNTTDiv64Initialization
import all FormalProof4FHE.HasteBoots.ConcreteNTTInitializedPower
import all FormalProof4FHE.HasteBoots.ConcreteNTTModularPower
import all FormalProof4FHE.HasteBoots.ConcreteNTTU256Mul128
import all FormalProof4FHE.HasteBoots.ConcreteNTTU256Add
import all FormalProof4FHE.HasteBoots.ConcreteNTTLimbAdd
import all FormalProof4FHE.HasteBoots.ConcreteNTTU256Mul64
import all FormalProof4FHE.HasteBoots.ConcreteNTTLimbArithmetic
import all FormalProof4FHE.HasteBoots.ConcreteNTTDiv64
import all FormalProof4FHE.HasteBoots.ReciprocalRemainder
import all Mathlib.Data.ZMod.Basic
import all Mathlib.Data.ZMod.Defs
import all Mathlib.Algebra.Group.Fin.Basic
import all FormalProof4FHE.HasteBoots.ConcreteNTTInitializedSearch
import all FormalProof4FHE.HasteBoots.ConcreteNTTInitializedSquareRoot
import all FormalProof4FHE.HasteBoots.ConcreteNTTInitializedRootConstruction
import all FormalProof4FHE.HasteBoots.ConcreteNTTWordSearch
import all FormalProof4FHE.HasteBoots.ConcreteNTTWordSquareRoot
import all FormalProof4FHE.HasteBoots.ConcreteNTTWordRootConstruction
import all FormalProof4FHE.HasteBoots.ConcreteNTTRootConstruction
import all FormalProof4FHE.HasteBoots.NativeFields

import all FormalProof4FHE.HasteBoots.ConcreteNTTMillerRabinField
import all FormalProof4FHE.HasteBoots.ConcreteNTTMillerRabinRound
import all FormalProof4FHE.HasteBoots.ConcreteNTTPrimeGate

import all FormalProof4FHE.HasteBoots.ConcreteNTTRootPowerArray
import all FormalProof4FHE.HasteBoots.ConcreteNTTPlanRootPowers

import all FormalProof4FHE.HasteBoots.ConcreteNTTBitReverse
import all FormalProof4FHE.HasteBoots.ConcreteNTTTwiddleIndices
import all FormalProof4FHE.HasteBoots.ConcreteNTTTwiddleArray
import all FormalProof4FHE.HasteBoots.ConcreteNTTConstructedTwiddles

import all FormalProof4FHE.HasteBoots.ConcreteNTTPlanConstants
import all FormalProof4FHE.HasteBoots.ConcreteNTTGoldPlan
import all FormalProof4FHE.HasteBoots.ConcreteNTTGoldTable

import all FormalProof4FHE.HasteBoots.ConcreteNTTCacheLookup
import all FormalProof4FHE.HasteBoots.ConcreteNTTGoldCache
import all FormalProof4FHE.HasteBoots.ConcreteNTTGoldCacheRCU

namespace FormalProof4FHETest.HasteBootsConcreteNTTGoldCacheSmoke
open FormalProof4FHE.HasteBoots
open ConcreteNTTLimbArithmetic (Limb)
private def fresh (logSize : Nat) (machine : ConcreteNTTGoldCacheRCU.Machine) : ConcreteNTTGoldCacheRCU.Attempt :=
  ConcreteNTTGoldCacheRCU.attempt logSize (ConcreteNTTGoldCacheRCU.capture machine) (ConcreteNTTGoldCacheRCU.newest machine)
private def freshRoot (logSize : Nat) (machine : ConcreteNTTGoldCacheRCU.Machine) : ConcreteNTTGoldCacheRCU.RootRead :=
  ConcreteNTTGoldCacheRCU.readRootSnapshot logSize (ConcreteNTTGoldCacheRCU.capture machine) (ConcreteNTTGoldCacheRCU.newest machine)

-- Literal first-match reads retain duplicate order and earlier values on append.
/-- info: true -/
#guard_msgs in
#eval decide (ConcreteNTTCacheLookup.lookup [(1,11),(1,12),(2,22)] 1 = some 11) &&
  decide (ConcreteNTTCacheLookup.lookup ([(1,11),(1,12)]++[(1,99)]) 1 = some 11) &&
  decide (ConcreteNTTCacheLookup.lookup ([(1,11)]++[(2,22)]) 2 = some 22)

-- Root misses retain exact native roots while dropping their temporary tables.
/-- info: true -/
#guard_msgs in
#eval [(4,70368744161280),(5,549755813888),(10,455906449640507599)].all fun (bits,expected) =>
  match ConcreteNTTGoldCache.getRoot bits {} with
  | .success root after => decide (root.val = expected ∧ after.tables = [] ∧ after.roots = [(bits,root)])
  | _ => false

-- Later table initialization preserves a root retained before any table existed.
/-- info: true -/
#guard_msgs in
#eval match ConcreteNTTGoldCache.getRoot 5 {} with
  | .success root before =>
    match ConcreteNTTGoldCache.initTable 5 before with
    | .success _ after =>
      match ConcreteNTTGoldCache.getTable 5 after with
      | .success table finalState => decide (table.root = root ∧ finalState.roots = before.roots ∧ finalState.tables.length = 1)
      | _ => false
    | _ => false
  | _ => false

-- Raw cache hits do not introduce a constructor-validation gate at read time.
/-- info: true -/
#guard_msgs in
#eval match ConcreteNTTGoldTable.newTable 5 with
  | .created table =>
    let state : ConcreteNTTGoldCache.State := ⟨[(3,table),(3,table)],[(3,7),(3,9)]⟩
    decide (ConcreteNTTGoldCache.getTable 3 state = ConcreteNTTGoldCache.Outcome.success table state) &&
    decide (ConcreteNTTGoldCache.getRoot 3 state = ConcreteNTTGoldCache.Outcome.success 7 state)
  | _ => false

-- The original root error and init/get-table callback unwrap panic are distinct.
/-- info: true -/
#guard_msgs in
#eval decide (ConcreteNTTGoldCache.getRoot 3 {} = ConcreteNTTGoldCache.Outcome.tableError) &&
  decide (ConcreteNTTGoldCache.initTable 3 {} = ConcreteNTTGoldCache.Outcome.assertionFailure) &&
  decide (ConcreteNTTGoldCache.getTable 3 {} = ConcreteNTTGoldCache.Outcome.assertionFailure)

-- Capture stores an actual current snapshot and does not mutate either cache.
/-- info: true -/
#guard_msgs in
#eval let machine : ConcreteNTTGoldCacheRCU.Machine := {}
  let captured := ConcreteNTTGoldCacheRCU.capture machine
  decide (captured.current = machine.current ∧ captured.version = 0 ∧ captured.snapshots.size = 1 ∧
    captured.snapshots[(ConcreteNTTGoldCacheRCU.newest machine).val] = ConcreteNTTGoldCacheRCU.Snapshot.mk 0 [])

-- Stale callbacks construct and retain the rejected proposal, without publication.
/-- info: true -/
#guard_msgs in
#eval let first := ConcreteNTTGoldCacheRCU.capture ({} : ConcreteNTTGoldCacheRCU.Machine)
  let second := ConcreteNTTGoldCacheRCU.capture first
  match ConcreteNTTGoldCacheRCU.attempt 5 second (ConcreteNTTGoldCacheRCU.newest first) with
  | .committed current =>
    if bound : 0 < current.snapshots.size then
      match ConcreteNTTGoldCacheRCU.attempt 10 current ⟨0,bound⟩ with
      | .retry proposal => decide (proposal.map Prod.fst = [10] ∧ current.current.tables.map Prod.fst = [5] ∧ current.version = 1)
      | _ => false
    else false
  | _ => false

-- A fresh retry appends the second key and preserves the earlier retained table.
/-- info: true -/
#guard_msgs in
#eval match fresh 5 {} with
  | .committed first =>
    match fresh 10 first with
    | .committed second => decide (second.current.tables.map Prod.fst = [5,10] ∧ second.version = 2 ∧
        ConcreteNTTCacheLookup.lookup second.current.tables 5 = ConcreteNTTCacheLookup.lookup first.current.tables 5)
    | _ => false
  | _ => false

-- A stale root-table view can generate a temporary Plan after table publication.
-- Merging that root preserves the newer published table and previously held root.
/-- info: true -/
#guard_msgs in
#eval match freshRoot 10 {} with
  | .success _ before =>
    let captured := ConcreteNTTGoldCacheRCU.capture before
    match ConcreteNTTGoldCacheRCU.attempt 5 captured (ConcreteNTTGoldCacheRCU.newest before) with
    | .committed published =>
      if bound : before.snapshots.size < published.snapshots.size then
        match ConcreteNTTGoldCacheRCU.readRootSnapshot 5 published ⟨before.snapshots.size,bound⟩ with
        | .success root after => decide (root.val = 549755813888 ∧ after.current.tables = published.current.tables ∧
            after.current.roots.map Prod.fst = [10,5] ∧ after.version = published.version)
        | _ => false
      else false
    | _ => false
  | _ => false

-- Repeated RCU inner checks preserve the retained vector and avoid duplicate keys.
/-- info: true -/
#guard_msgs in
#eval match fresh 5 {} with
  | .committed before =>
    match fresh 5 before with
    | .committed after => decide (after.current.tables = before.current.tables ∧ after.current.tables.length = 1 ∧ after.version = 2)
    | _ => false
  | _ => false

-- Root cache hits survive both intervening table publication and further captures.
/-- info: true -/
#guard_msgs in
#eval match freshRoot 5 {} with
  | .success root before =>
    match fresh 5 before with
    | .committed published =>
      match freshRoot 5 published with
      | .success repeated after => decide (repeated = root ∧ after.current = published.current)
      | _ => false
    | _ => false
  | _ => false

end FormalProof4FHETest.HasteBootsConcreteNTTGoldCacheSmoke
