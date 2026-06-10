use std::env;
use std::path::PathBuf;
use std::process;

fn main() {
    let mut args = env::args_os();
    let program = args
        .next()
        .map(PathBuf::from)
        .and_then(|path| path.file_name().map(|name| name.to_owned()))
        .and_then(|name| name.into_string().ok())
        .unwrap_or_else(|| "yulang2".to_string());

    let Some(command) = args.next() else {
        print_usage_and_exit(&program);
    };

    match command.to_str() {
        Some("dump-poly") => {
            let Some(path) = args.next() else {
                print_usage_and_exit(&program);
            };
            if args.next().is_some() {
                print_usage_and_exit(&program);
            }
            match yulang2::dump_poly_from_entry(PathBuf::from(path)) {
                Ok(output) => print!("{}", output.text),
                Err(error) => {
                    eprintln!("{error}");
                    process::exit(1);
                }
            }
        }
        Some("dump-poly-std") => {
            let Some(path) = args.next() else {
                print_usage_and_exit(&program);
            };
            if args.next().is_some() {
                print_usage_and_exit(&program);
            }
            match yulang2::dump_poly_from_entry_with_std(PathBuf::from(path)) {
                Ok(output) => {
                    print!("{}", output.text);
                    for error in &output.errors {
                        eprintln!("error: {error}");
                    }
                }
                Err(error) => {
                    eprintln!("{error}");
                    process::exit(1);
                }
            }
        }
        _ => print_usage_and_exit(&program),
    }
}

fn print_usage_and_exit(program: &str) -> ! {
    eprintln!("usage: {program} dump-poly <path>");
    eprintln!("       {program} dump-poly-std <path>");
    process::exit(2);
}
