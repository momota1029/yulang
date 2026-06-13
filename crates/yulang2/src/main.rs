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
                Ok(output) => print_dump_poly_output(&output),
                Err(error) => {
                    eprintln!("{error}");
                    process::exit(1);
                }
            }
        }
        Some("dump-poly-raw") => {
            let Some(path) = args.next() else {
                print_usage_and_exit(&program);
            };
            if args.next().is_some() {
                print_usage_and_exit(&program);
            }
            match yulang2::dump_poly_raw_from_entry(PathBuf::from(path)) {
                Ok(output) => print_dump_poly_output(&output),
                Err(error) => {
                    eprintln!("{error}");
                    process::exit(1);
                }
            }
        }
        Some("dump-mono") => {
            let Some(path) = args.next() else {
                print_usage_and_exit(&program);
            };
            if args.next().is_some() {
                print_usage_and_exit(&program);
            }
            match yulang2::dump_mono_from_entry(PathBuf::from(path)) {
                Ok(output) => print_dump_mono_output(&output),
                Err(error) => {
                    eprintln!("{error}");
                    process::exit(1);
                }
            }
        }
        Some("run-mono") => {
            let Some(path) = args.next() else {
                print_usage_and_exit(&program);
            };
            if args.next().is_some() {
                print_usage_and_exit(&program);
            }
            match yulang2::run_mono_from_entry(PathBuf::from(path)) {
                Ok(output) => print_run_mono_output(&output),
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
                Ok(output) => print_dump_poly_output(&output),
                Err(error) => {
                    eprintln!("{error}");
                    process::exit(1);
                }
            }
        }
        Some("dump-mono-std") => {
            let Some(path) = args.next() else {
                print_usage_and_exit(&program);
            };
            if args.next().is_some() {
                print_usage_and_exit(&program);
            }
            match yulang2::dump_mono_from_entry_with_std(PathBuf::from(path)) {
                Ok(output) => print_dump_mono_output(&output),
                Err(error) => {
                    eprintln!("{error}");
                    process::exit(1);
                }
            }
        }
        Some("run-mono-std") => {
            let Some(path) = args.next() else {
                print_usage_and_exit(&program);
            };
            if args.next().is_some() {
                print_usage_and_exit(&program);
            }
            match yulang2::run_mono_from_entry_with_std(PathBuf::from(path)) {
                Ok(output) => print_run_mono_output(&output),
                Err(error) => {
                    eprintln!("{error}");
                    process::exit(1);
                }
            }
        }
        Some("check-poly-std") => {
            let Some(path) = args.next() else {
                print_usage_and_exit(&program);
            };
            if args.next().is_some() {
                print_usage_and_exit(&program);
            }
            match yulang2::check_poly_from_entry_with_std(PathBuf::from(path)) {
                Ok(output) => print_check_poly_output(&output),
                Err(error) => {
                    eprintln!("{error}");
                    process::exit(1);
                }
            }
        }
        Some("check-poly-std-in") => {
            let Some(path) = args.next() else {
                print_usage_and_exit(&program);
            };
            let Some(module) = args.next() else {
                print_usage_and_exit(&program);
            };
            if args.next().is_some() {
                print_usage_and_exit(&program);
            }
            let Some(module) = module.to_str() else {
                print_usage_and_exit(&program);
            };
            match yulang2::check_poly_from_entry_with_std_in_module(PathBuf::from(path), module) {
                Ok(output) => print_check_poly_output(&output),
                Err(error) => {
                    eprintln!("{error}");
                    process::exit(1);
                }
            }
        }
        Some("dump-poly-std-in") => {
            let Some(path) = args.next() else {
                print_usage_and_exit(&program);
            };
            let Some(module) = args.next() else {
                print_usage_and_exit(&program);
            };
            if args.next().is_some() {
                print_usage_and_exit(&program);
            }
            let Some(module) = module.to_str() else {
                print_usage_and_exit(&program);
            };
            match yulang2::dump_poly_from_entry_with_std_in_module(PathBuf::from(path), module) {
                Ok(output) => print_dump_poly_output(&output),
                Err(error) => {
                    eprintln!("{error}");
                    process::exit(1);
                }
            }
        }
        Some("dump-poly-std-raw") => {
            let Some(path) = args.next() else {
                print_usage_and_exit(&program);
            };
            if args.next().is_some() {
                print_usage_and_exit(&program);
            }
            match yulang2::dump_poly_raw_from_entry_with_std(PathBuf::from(path)) {
                Ok(output) => print_dump_poly_output(&output),
                Err(error) => {
                    eprintln!("{error}");
                    process::exit(1);
                }
            }
        }
        Some("dump-poly-std-in-raw") => {
            let Some(path) = args.next() else {
                print_usage_and_exit(&program);
            };
            let Some(module) = args.next() else {
                print_usage_and_exit(&program);
            };
            if args.next().is_some() {
                print_usage_and_exit(&program);
            }
            let Some(module) = module.to_str() else {
                print_usage_and_exit(&program);
            };
            match yulang2::dump_poly_raw_from_entry_with_std_in_module(PathBuf::from(path), module)
            {
                Ok(output) => print_dump_poly_output(&output),
                Err(error) => {
                    eprintln!("{error}");
                    process::exit(1);
                }
            }
        }
        _ => print_usage_and_exit(&program),
    }
}

fn print_dump_poly_output(output: &yulang2::DumpPolyOutput) {
    print!("{}", output.text);
    for error in &output.errors {
        eprintln!("error: {error}");
    }
}

fn print_dump_mono_output(output: &yulang2::DumpMonoOutput) {
    print!("{}", output.text);
    for error in &output.errors {
        eprintln!("error: {error}");
    }
}

fn print_run_mono_output(output: &yulang2::RunMonoOutput) {
    print!("{}", output.text);
    for error in &output.errors {
        eprintln!("error: {error}");
    }
}

fn print_check_poly_output(output: &yulang2::CheckPolyOutput) {
    print!("{}", output.text);
}

fn print_usage_and_exit(program: &str) -> ! {
    eprintln!("usage: {program} dump-poly <path>");
    eprintln!("       {program} dump-poly-raw <path>");
    eprintln!("       {program} dump-mono <path>");
    eprintln!("       {program} run-mono <path>");
    eprintln!("       {program} dump-poly-std <path>");
    eprintln!("       {program} dump-mono-std <path>");
    eprintln!("       {program} run-mono-std <path>");
    eprintln!("       {program} check-poly-std <path>");
    eprintln!("       {program} check-poly-std-in <path> <module>");
    eprintln!("       {program} dump-poly-std-in <path> <module>");
    eprintln!("       {program} dump-poly-std-raw <path>");
    eprintln!("       {program} dump-poly-std-in-raw <path> <module>");
    process::exit(2);
}
