module
public import FormalProof4FHE.HasteBoots.LookupTupleTest
public import FormalProof4FHE.HasteBoots.LookupProducerArithmetic
@[expose] public section

/-! Validated rectangular public rows give exact native finite tuples, not
zero-filled replacements. Native compression preserves their original row
order, raw words and semantic tuple hash. -/
namespace FormalProof4FHE.HasteBoots.LookupValidatedPublicTable
open NativeSharedLookupStatement (Request)
open NativeFieldRepresentation (GoldWord goldValue)
open NativeExtensionFields (Goldilocks3)
noncomputable section

def rawRows (request : Request) (rectangular : ∀ row ∈ request.table, row.length = request.columns) :
    Fin request.table.length → Fin request.columns → GoldWord :=
  fun row column => (request.table.get row)[column.val]'(by
    rw [rectangular _ (List.get_mem _ _)]
    exact column.isLt)

theorem rawRows_exact (request : Request) (rectangular : ∀ row ∈ request.table, row.length = request.columns) :
    List.ofFn (fun row => List.ofFn (rawRows request rectangular row)) = request.table := by
  apply List.ext_getElem (by simp)
  intro row leftBound rightBound
  rw [List.getElem_ofFn]
  apply List.ext_getElem (by simp only [List.length_ofFn]; exact (rectangular _ (List.getElem_mem rightBound)).symm)
  intro column leftColumn rightColumn
  rw [List.getElem_ofFn]
  rfl

theorem publicRows_eq (request : Request) (rectangular : ∀ row ∈ request.table, row.length = request.columns)
    (row : Fin request.table.length) (column : Fin request.columns) :
    LookupTupleTest.publicRows request row column = goldValue (rawRows request rectangular row column) := by
  have inside : column.val < (request.table.get row).length := by
    rw [rectangular _ (List.get_mem _ _)]
    exact column.isLt
  simp only [LookupTupleTest.publicRows,List.getElem?_map,List.getElem?_eq_getElem inside,Option.map_some,Option.getD_some,rawRows]

theorem native_table (request : Request) (rectangular : ∀ row ∈ request.table, row.length = request.columns)
    (y : NativeGoldExtensionArithmetic.Word) :
    (NativeGoldLookup.tableAt request.table request.columns y).map NativeFieldWire.goldExtensionValue =
      List.ofFn (fun row => TupleHash.hash (NativeFieldWire.goldExtensionValue y) (LookupTupleTest.publicRows request row)) := by
  have rows : request.table.map (List.map goldValue) =
      List.ofFn (fun row => List.ofFn (fun column => goldValue (rawRows request rectangular row column))) := by
    have mapped := congrArg (List.map (List.map goldValue)) (rawRows_exact request rectangular).symm
    simpa only [List.map_ofFn,Function.comp_def] using mapped
  rw [NativeGoldLookup.tableAt_value,rows,NativeLookupArithmetic.tableAt_vectors]
  congr 1
  funext row
  congr 1
  funext column
  exact (publicRows_eq request rectangular row column).symm

theorem produced_total (request : Request) (rectangular : ∀ row ∈ request.table, row.length = request.columns)
    (selection : NativeLookupChallenge.Machine Goldilocks3) (output : NativeGoldLookupProducer.Output)
    (produced : NativeGoldLookupProducer.produce request.columns request.table selection = some output)
    (counts : Fin request.table.length → GoldWord) :
    NativeFieldWire.goldExtensionValue (NativeGoldExtensionArithmetic.tableSum output.inverses (List.ofFn counts)) =
      LookupPairArithmetic.tableSum (NativeFieldWire.goldExtensionValue output.r) (NativeFieldWire.goldExtensionValue output.y)
        (LookupTupleTest.publicRows request) (fun row => goldValue (counts row)) := by
  have native := produced
  rw [← rawRows_exact request rectangular] at native
  have total := LookupProducerArithmetic.public_total_vectors (rawRows request rectangular) counts native
  have rows : (fun row column => goldValue (rawRows request rectangular row column)) = LookupTupleTest.publicRows request := by
    funext row column
    exact (publicRows_eq request rectangular row column).symm
  rwa [rows] at total

theorem produced_domain (request : Request) (rectangular : ∀ row ∈ request.table, row.length = request.columns)
    (selection : NativeLookupChallenge.Machine Goldilocks3) (output : NativeGoldLookupProducer.Output)
    (produced : NativeGoldLookupProducer.produce request.columns request.table selection = some output) :
    NativeFieldWire.goldExtensionValue output.r ≠ 0 ∧ ∀ row,
      NativeFieldWire.goldExtensionValue output.r + TupleHash.hash (NativeFieldWire.goldExtensionValue output.y) (LookupTupleTest.publicRows request row) ≠ 0 := by
  have spec := LookupProducerArithmetic.produced produced
  refine ⟨spec.2.1,?_⟩
  have poles := spec.2.2.1
  rw [spec.1,native_table request rectangular output.y] at poles
  exact fun row => poles _ (List.mem_ofFn.mpr ⟨row,rfl⟩)

end
end FormalProof4FHE.HasteBoots.LookupValidatedPublicTable
