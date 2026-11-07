//! Public-cache regression against unchanged pinned HasteBoots, not a refinement proof.
use algebra::{Field, Goldilocks, NTTField, transformation::AbstractNTT};
use std::sync::{Arc, Barrier};

#[derive(Clone, Debug, Default)]
struct ContextSpy {
    bytes: Vec<u8>,
}
static CONTEXT_INPUTS: std::sync::Mutex<Vec<Vec<u8>>> = std::sync::Mutex::new(Vec::new());
impl pcs::utils::hash::Hash for ContextSpy {
    type Output = pcs::utils::hash::Digest512;
    fn update_hash_value(&mut self, input: &[u8]) {
        self.bytes.extend_from_slice(input);
    }
    fn output_reset(&mut self) -> Self::Output {
        use pcs::utils::hash::Hash;
        let input = std::mem::take(&mut self.bytes);
        let mut hash = <sha2::Sha512 as Hash>::new();
        hash.update_hash_value(&input);
        let result = hash.output_reset();
        CONTEXT_INPUTS.lock().unwrap().push(input);
        result
    }
}
fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}
fn parameters() {
    use pcs::{
        matrix_weighted::Parameters,
        utils::{code::BlockReedSolomonCode, hash::Digest512},
    };
    for (num_vars, width, left, queries, message, block, blowup) in [
        (5, 3, 2, 2, 8, 3, 2),
        (6, 4, 2, 3, 16, 4, 4),
        (12, 4, 2, 8, 1024, 4, 4),
    ] {
        let code = BlockReedSolomonCode::<Goldilocks>::new(message, block, blowup).unwrap();
        let original = bincode::serde::encode_to_vec(&code, bincode::config::standard()).unwrap();
        let params =
            Parameters::new_encoded::<Goldilocks>(num_vars, width, left, queries, code).unwrap();
        assert_eq!(
            (
                params.num_vars(),
                params.width(),
                params.left_vars(),
                params.queries()
            ),
            (num_vars, width, left, queries)
        );
        let retained =
            bincode::serde::encode_to_vec(params.code(), bincode::config::standard()).unwrap();
        assert_eq!(original, retained);
        let Digest512(digest) = params.context_digest::<Goldilocks, ContextSpy>().unwrap();
        assert_eq!(
            Digest512(digest),
            params.context_digest::<Goldilocks, sha2::Sha512>().unwrap()
        );
        let input = CONTEXT_INPUTS.lock().unwrap().pop().unwrap();
        println!(
            "PARAM {num_vars} {width} {left} {queries} {message} {block} {blowup} {} {} {}",
            hex(&retained),
            hex(&input),
            hex(&digest)
        );
    }
    for (name, num_vars, width, left, queries, expected) in [
        (
            "width-zero",
            0,
            0,
            0,
            1,
            "invalid dimensions or query count",
        ),
        (
            "left-too-large",
            0,
            1,
            1,
            1,
            "invalid dimensions or query count",
        ),
        (
            "variables-too-large",
            64,
            1,
            0,
            1,
            "invalid dimensions or query count",
        ),
        (
            "queries-zero",
            0,
            1,
            0,
            0,
            "invalid dimensions or query count",
        ),
        (
            "code-shape",
            1,
            1,
            0,
            1,
            "code dimensions do not match table",
        ),
        ("table-overflow", 63, 2, 63, 1, "table size overflow"),
        ("encoded-overflow", 63, 1, 63, 1, "encoded size overflow"),
        (
            "linear-overflow",
            0,
            1_usize << 32,
            0,
            1,
            "linear-test matrix size overflow",
        ),
    ] {
        let code = BlockReedSolomonCode::<Goldilocks>::new(1, 1, 2).unwrap();
        let error = Parameters::new_encoded::<Goldilocks>(num_vars, width, left, queries, code)
            .err()
            .expect("must reject");
        assert_eq!(error.0, expected);
        println!("PARAM_ERROR {name}");
    }
    // Exercise the generic API's final guard without pretending this descriptor
    // has BlockReedSolomonCode::new provenance (that type is not Deserialize).
    struct HugeTree;
    impl pcs::utils::code::RowCode<Goldilocks> for HugeTree {
        fn message_len(&self) -> usize {
            1
        }
        fn block_width(&self) -> usize {
            1
        }
        fn codeword_blocks(&self) -> usize {
            1_usize << 63
        }
        fn distance(&self) -> f64 {
            0.0
        }
        fn proximity_gap(&self) -> f64 {
            0.0
        }
        fn domain_separator(&self) -> &'static [u8] {
            b"fixture-only-invalid-tree"
        }
        fn encode_row(&self, _: &[Goldilocks], _: &mut [Goldilocks]) {
            panic!("must reject before encoding")
        }
    }
    let error = Parameters::new_encoded::<Goldilocks>(0, 1, 0, 1, HugeTree)
        .err()
        .expect("Merkle size must reject");
    assert_eq!(error.0, "Merkle tree size overflow");
    println!("PARAM_ERROR merkle-overflow");
}

fn balanced_parameters() {
    use pcs::{
        matrix_weighted::Parameters,
        utils::{code::BlockReedSolomonCode, hash::Digest512},
    };
    for (n, w, q, b) in [
        (0, 3, 1, 2),
        (2, 4, 1, 2),
        (5, 3, 2, 2),
        (10, 3, 128, 2),
        (10, 4, 128, 4),
        (16, 4, 64, 2),
    ] {
        let params =
            Parameters::<BlockReedSolomonCode<Goldilocks>>::balanced_block_rs(n, w, q, b).unwrap();
        let code =
            bincode::serde::encode_to_vec(params.code(), bincode::config::standard()).unwrap();
        let Digest512(digest) = params.context_digest::<Goldilocks, ContextSpy>().unwrap();
        let input = CONTEXT_INPUTS.lock().unwrap().pop().unwrap();
        println!(
            "BALANCED {n} {w} {q} {b} {} {} {} {}",
            params.left_vars(),
            hex(&code),
            hex(&input),
            hex(&digest)
        );
    }
    for (name, n, w, q, b, expected) in [
        (
            "width-zero",
            0,
            0,
            1,
            2,
            "invalid block RS layout parameters",
        ),
        (
            "queries-zero",
            0,
            1,
            0,
            2,
            "invalid block RS layout parameters",
        ),
        (
            "variables-too-large",
            64,
            1,
            1,
            2,
            "invalid block RS layout parameters",
        ),
        (
            "small-blowup",
            0,
            1,
            1,
            1,
            "invalid block RS layout parameters",
        ),
        (
            "nonpower-blowup",
            0,
            1,
            1,
            3,
            "invalid block RS layout parameters",
        ),
        ("table-overflow", 63, 2, 1, 2, "table size overflow"),
        (
            "unsupported-layout",
            0,
            1,
            1,
            1_usize << 63,
            "no supported block RS layout",
        ),
    ] {
        let error = Parameters::<BlockReedSolomonCode<Goldilocks>>::balanced_block_rs(n, w, q, b)
            .err()
            .expect("must reject");
        assert_eq!(error.0, expected);
        println!("BALANCED_ERROR {name}");
    }
}

fn block_codes() {
    use pcs::utils::code::{BlockReedSolomonCode, RowCode};
    for (message, block, blowup) in [(1, 1, 2), (7, 3, 2), (1024, 4, 4), (4096, 4, 4)] {
        let code = BlockReedSolomonCode::<Goldilocks>::new(message, block, blowup).unwrap();
        let count = code.codeword_blocks();
        let root = Goldilocks::get_ntt_table(count.ilog2())
            .unwrap()
            .root()
            .value();
        let bytes = bincode::serde::encode_to_vec(&code, bincode::config::standard()).unwrap();
        let (decoded, used): ((usize, usize, usize, usize, String, u64), usize) =
            bincode::serde::decode_from_slice(&bytes, bincode::config::standard()).unwrap();
        assert_eq!(used, bytes.len());
        assert_eq!(
            decoded,
            (
                message,
                block,
                code.message_blocks(),
                count,
                Goldilocks::MODULUS_VALUE.to_string(),
                root
            )
        );
        let reference =
            concrete_ntt::prime64::Plan::try_new(count, Goldilocks::MODULUS_VALUE).unwrap();
        assert_eq!(root, reference.root());
        let hex: String = bytes.iter().map(|byte| format!("{byte:02x}")).collect();
        println!(
            "BLOCK {message} {block} {blowup} {} {count} {root} {hex}",
            code.message_blocks()
        );
    }
    for (name, message, block, blowup, expected) in [
        (
            "zero-message",
            0,
            1,
            2,
            "invalid block RS dimensions or blowup",
        ),
        (
            "zero-block",
            1,
            0,
            2,
            "invalid block RS dimensions or blowup",
        ),
        (
            "small-blowup",
            1,
            1,
            1,
            "invalid block RS dimensions or blowup",
        ),
        (
            "nonpower-blowup",
            1,
            1,
            3,
            "invalid block RS dimensions or blowup",
        ),
        (
            "message-overflow",
            usize::MAX,
            1,
            2,
            "block RS message size overflow",
        ),
        (
            "domain-overflow",
            1_usize << 63,
            1,
            2,
            "block RS domain overflow",
        ),
        (
            "stride-overflow",
            1,
            usize::MAX,
            2,
            "block RS codeword size overflow",
        ),
        (
            "unsupported-domain",
            1_usize << 31,
            1,
            2,
            "unsupported block RS NTT domain",
        ),
    ] {
        let error = BlockReedSolomonCode::<Goldilocks>::new(message, block, blowup)
            .err()
            .expect("must reject");
        assert_eq!(error, expected);
        println!("BLOCK_ERROR {name}");
    }
}

fn main() {
    assert_eq!(usize::BITS, 64);
    const LOGS: [u32; 3] = [4, 5, 10];
    const WORKERS: usize = 8;
    let mut roots = Vec::new();
    // Fresh-process root reads precede every table initialization.
    for log in LOGS {
        let root = Goldilocks::get_ntt_root(log).unwrap().value();
        let reference =
            concrete_ntt::prime64::Plan::try_new(1 << log, Goldilocks::MODULUS_VALUE).unwrap();
        assert_eq!(root, reference.root());
        roots.push(root);
        println!("CACHE_PRE {log} {root}");
    }
    let barrier = Arc::new(Barrier::new(WORKERS));
    let mut workers = Vec::new();
    for worker in 0..WORKERS {
        let barrier = Arc::clone(&barrier);
        workers.push(std::thread::spawn(move || {
            barrier.wait();
            let mut handles = Vec::new();
            for offset in 0..LOGS.len() {
                let log = LOGS[(worker + offset) % LOGS.len()];
                Goldilocks::init_ntt_table(log).unwrap();
                handles.push((log, Goldilocks::get_ntt_table(log).unwrap()));
            }
            handles
        }));
    }
    let handles: Vec<_> = workers
        .into_iter()
        .flat_map(|worker| worker.join().unwrap())
        .collect();
    for (slot, log) in LOGS.into_iter().enumerate() {
        let table = Goldilocks::get_ntt_table(log).unwrap();
        let repeated = Goldilocks::get_ntt_table(log).unwrap();
        assert!(Arc::ptr_eq(&table, &repeated));
        let mut count = 0;
        for (key, handle) in &handles {
            if *key == log {
                assert!(Arc::ptr_eq(&table, handle));
                count += 1;
            }
        }
        assert_eq!(count, WORKERS);
        assert_eq!(table.root().value(), roots[slot]);
        assert_eq!(Goldilocks::get_ntt_root(log).unwrap().value(), roots[slot]);
        println!("CACHE_AFTER {log} {} {count}", table.root().value());
    }
    // Root generation propagates the table error; init's callback unwrap panics.
    assert!(Goldilocks::get_ntt_root(3).is_err());
    let before = Goldilocks::get_ntt_table(5).unwrap();
    let hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let panicked = std::panic::catch_unwind(|| Goldilocks::init_ntt_table(3)).is_err();
    std::panic::set_hook(hook);
    assert!(panicked);
    assert!(Arc::ptr_eq(&before, &Goldilocks::get_ntt_table(5).unwrap()));
    assert_eq!(Goldilocks::get_ntt_root(5).unwrap().value(), roots[1]);
    println!("CACHE_ERROR root-error=true init-panic=true retained-stable=true");
    println!("CACHE_OK workers=8 logs=3 retained-handles=24");
    block_codes();
    parameters();
    balanced_parameters();
}
