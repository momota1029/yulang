//! Offline standalone counterpart of the subprocess stack regression.
#[path = "support/nesting_cases.rs"]
mod cases;

fn main() {
    let args: Vec<_> = std::env::args().collect();
    if args.get(1).is_some_and(|s| s == "--case") {
        let source = cases::source(&args[2], args[3].parse().unwrap(), args[4] == "balanced");
        println!("limited={}", cases::check(&source));
        return;
    }
    for stack_size in [2 * 1024 * 1024, 512 * 1024] {
        eprintln!("STACK {stack_size}");
        std::thread::Builder::new()
            .stack_size(stack_size)
            .spawn(cases::stress)
            .unwrap()
            .join()
            .unwrap();
    }
}
