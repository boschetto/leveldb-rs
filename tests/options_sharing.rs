use rusty_leveldb::Options;
use std::thread;

#[test]
fn test_options_send() {
    let opt = Options::default();
    let handle = thread::spawn(move || {
        let _ = opt;
    });
    handle.join().unwrap();
}

#[test]
fn test_options_clone_send() {
    let opt = Options::default();
    let opt2 = opt.clone();
    let handle = thread::spawn(move || {
        let _ = opt2;
    });
    handle.join().unwrap();
    // Verify original still usable
    let _ = opt;
}
