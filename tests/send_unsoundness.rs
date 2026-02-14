use rusty_leveldb::{Options, DB};
use std::thread;
use std::sync::{Arc, Barrier};
use std::time::Duration;

#[test]
fn test_send_rc_race() {
    // We run this in a loop to increase the chance of catching the race.
    // A Segfault or "double free" or random memory corruption is expected if this races.
    for _ in 0..100 {
        let opt = rusty_leveldb::in_memory();
        let opt_clone = opt.clone();

        // Create DB. DB takes ownership of one Options.
        // In-memory options use MemEnv.
        let db = DB::open("test_send_race", opt).unwrap();

        // Barrier to sync drop timing (approximate)
        let barrier = Arc::new(Barrier::new(2));
        let b2 = barrier.clone();

        let t = thread::spawn(move || {
            let _db = db; // Move DB into thread
            b2.wait();
            // Drop _db happens here
        });

        barrier.wait();
        // Drop opt_clone happens here
        drop(opt_clone);

        t.join().unwrap();
    }
}
