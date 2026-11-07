//! Public-cache regression against unchanged pinned HasteBoots, not a refinement proof.
use algebra::{Field, Goldilocks, NTTField, transformation::AbstractNTT};
use std::sync::{Arc, Barrier};

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
}
