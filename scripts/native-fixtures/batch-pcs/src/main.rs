//! Deterministic native evidence for the Lean batch PCS regression fixtures.
//! All cases run in one uniquely named executable, with explicit result markers.
use algebra::{
    Field, Goldilocks as F,
    matrix_weighted::{Matrix, MatrixPair, PackedTable},
};
use helper::{
    FiatShamirTranscript, Transcript,
    classical_transcript::audit::{self, ReaderEvent},
};
use pcs::{
    matrix_weighted::Parameters,
    utils::{
        code::BlockReedSolomonCode,
        hash::{Digest512, Hash},
    },
};
use serde::Serialize;
use std::sync::{Arc, Mutex};

type HashObservation = (Vec<u8>, Vec<u8>);
// kind 0 = start, 1 = output, 2 = hash; input, byte offset, answer bytes.
type Observation = (u8, Vec<u8>, u128, Vec<u8>);
static HASHES: Mutex<Vec<HashObservation>> = Mutex::new(Vec::new());
static OBSERVATIONS: Mutex<Vec<Observation>> = Mutex::new(Vec::new());

#[derive(Debug, Clone, Default)]
struct Spy {
    bytes: Vec<u8>,
}
impl Hash for Spy {
    type Output = Digest512;
    fn update_hash_value(&mut self, bytes: &[u8]) {
        self.bytes.extend_from_slice(bytes);
    }
    fn output_reset(&mut self) -> Digest512 {
        let input = std::mem::take(&mut self.bytes);
        let mut hash = <sha2::Sha512 as Hash>::new();
        hash.update_hash_value(&input);
        let output = hash.output_reset();
        HASHES
            .lock()
            .unwrap()
            .push((input.clone(), output.0.to_vec()));
        OBSERVATIONS
            .lock()
            .unwrap()
            .push((2, input, 0, output.0.to_vec()));
        output
    }
}
fn encode<T: Serialize + ?Sized>(value: &T) -> Vec<u8> {
    bincode::serde::encode_to_vec(value, bincode::config::standard()).unwrap()
}
// Deserialization deliberately preserves the native lazy representative p of zero.
fn word(value: u64) -> F {
    bincode::serde::decode_from_slice(&encode(&value), bincode::config::standard())
        .unwrap()
        .0
}
fn pair(zero: u64, one: u64) -> MatrixPair<F> {
    MatrixPair {
        zero: Matrix::new(1, vec![word(zero)]).unwrap(),
        one: Matrix::new(1, vec![word(one)]).unwrap(),
    }
}
#[derive(Clone, Copy)]
enum Case {
    Accepted,
    LastClaim,
    SecondResponse,
}
impl Case {
    fn name(self) -> &'static str {
        match self {
            Self::Accepted => "accepted",
            Self::LastClaim => "last-claim",
            Self::SecondResponse => "second-response",
        }
    }
}
fn exercise(case: Case) {
    let code = BlockReedSolomonCode::<F>::new(2, 2, 2).unwrap();
    let parameters = Parameters::new_encoded::<F>(2, 1, 1, 1, code).unwrap();
    let queries = vec![
        vec![pair(0, 1), pair(1, 0)],
        vec![pair(0, 1), pair(2, 3)],
        vec![pair(1, 0), pair(0, 1)],
        vec![pair(F::MODULUS_VALUE, 1), pair(1, 0)],
    ];
    let cells = match case {
        Case::Accepted => (0..4).map(F::new).collect(),
        _ => vec![F::new(0); 4],
    };
    let table = PackedTable::new(2, 1, cells).unwrap();
    let (root, state) = parameters.commit::<F, Spy>(&table).unwrap();
    let mut values = queries
        .iter()
        .map(|query| table.evaluate(query).unwrap())
        .collect::<Vec<_>>();
    let mut prover = Transcript::<F>::new_classical_atomic_columns(&[0; 64]);
    let mut opening = parameters
        .open_many::<F, Spy>(&mut prover, &root, &state, &queries, &values)
        .unwrap();
    assert_eq!(opening.evaluations.len(), 2);
    match case {
        Case::Accepted => {}
        Case::LastClaim => values[3][0] = F::new(1),
        Case::SecondResponse => opening.evaluations[1][0] = F::new(1),
    }
    HASHES.lock().unwrap().clear();
    OBSERVATIONS.lock().unwrap().clear();
    let starts = Arc::new(Mutex::new(Vec::<Vec<u8>>::new()));
    let outputs = Arc::new(Mutex::new(Vec::<(u64, u128, Vec<u8>)>::new()));
    let (captured_starts, captured_outputs) = (starts.clone(), outputs.clone());
    let guard = audit::observe_with_reader_events(
        |_| {},
        move |event| match event {
            ReaderEvent::Start { reader, input } => {
                let mut all = captured_starts.lock().unwrap();
                assert_eq!(reader as usize, all.len());
                all.push(input.to_vec());
                OBSERVATIONS
                    .lock()
                    .unwrap()
                    .push((0, input.to_vec(), 0, vec![]));
            }
            ReaderEvent::Output {
                reader,
                offset,
                bytes,
            } => {
                let input = captured_starts.lock().unwrap()[reader as usize].clone();
                captured_outputs
                    .lock()
                    .unwrap()
                    .push((reader, offset, bytes.to_vec()));
                OBSERVATIONS
                    .lock()
                    .unwrap()
                    .push((1, input, offset, bytes.to_vec()));
            }
        },
    )
    .unwrap();
    let mut verifier = Transcript::<F>::new_classical_atomic_columns(&[0; 64]);
    let result =
        parameters.verify_many::<F, Spy>(&mut verifier, &root, &queries, &values, &opening);
    match case {
        Case::Accepted => result.unwrap(),
        Case::LastClaim => assert_eq!(
            format!("{:?}", result.unwrap_err()),
            "Error(\"incorrect batch opening value\")"
        ),
        Case::SecondResponse => assert_eq!(
            format!("{:?}", result.unwrap_err()),
            "Error(\"batch structured response mismatch\")"
        ),
    }
    let verifier_observations = OBSERVATIONS.lock().unwrap().clone();
    assert_eq!(HASHES.lock().unwrap().len(), 7);
    assert_eq!(starts.lock().unwrap().len(), 3);
    assert_eq!(outputs.lock().unwrap().len(), 4);
    assert_eq!(verifier_observations.len(), 14);
    // Probe the actual final parent, then remove only this probe's request frame.
    let label = b"after native batch fixture";
    verifier.get_challenge_bytes(label, &mut [0; 1]);
    drop(guard);
    let all_starts = starts.lock().unwrap().clone();
    assert_eq!(all_starts.len(), 4);
    let mut suffix = vec![2];
    suffix.extend_from_slice(&(label.len() as u64).to_le_bytes());
    suffix.extend_from_slice(label);
    suffix.extend_from_slice(&8u64.to_le_bytes());
    suffix.extend_from_slice(&1u64.to_le_bytes());
    assert!(all_starts[3].ends_with(&suffix));
    let final_parent = &all_starts[3][..all_starts[3].len() - suffix.len()];
    let hashes = HASHES.lock().unwrap().clone();
    println!("CASE {}", case.name());
    println!("ROOT {:?}", root.root.0.to_vec());
    println!("QUERIES {:?}", encode(&queries));
    println!("VALUES {:?}", encode(&values));
    println!("OPENING {:?}", encode(&opening));
    println!("CONTEXT_INPUT {:?}", hashes[0].0);
    println!("CONTEXT_DIGEST {:?}", hashes[0].1);
    println!("FIRST_START {:?}", all_starts[0]);
    println!("STARTS {all_starts:?}");
    println!("OUTPUTS {:?}", outputs.lock().unwrap());
    println!("HASHES {hashes:?}");
    println!("OBSERVATIONS {verifier_observations:?}");
    println!("FINAL_PARENT {final_parent:?}");
    println!("CASE_OK {}", case.name());
}
fn main() {
    for case in [Case::Accepted, Case::LastClaim, Case::SecondResponse] {
        exercise(case);
    }
}
