//! Public-cache regression against unchanged pinned HasteBoots, not a refinement proof.
use algebra::{Field, Goldilocks, NTTField, transformation::AbstractNTT};
use std::sync::{Arc, Barrier};

fn main() {
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
}
