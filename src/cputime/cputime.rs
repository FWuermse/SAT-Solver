use clap::{command, Arg};
use std::{
    fs,
    io::{BufWriter, Write},
    path::Path,
    process::{Command, Output},
    str,
    sync::mpsc,
    thread,
    time::{Duration, Instant},
};

fn main() {
    let matches = command!()
        .arg(
            Arg::new("use_time_limit")
                .short('t')
                .long("time-limit")
                .default_value("true")
                .help("Set to 'false' to disable the 60 seconds time limit"),
        )
        .arg(
            Arg::new("heuristic")
                .short('H')
                .long("heuristic")
                .default_value("arbitrary")
                .help("Heuristic to be used in the solver"),
        )
        .get_matches();

    let use_time_limit = matches.get_one::<String>("use_time_limit").map(|s| s == "true").unwrap();
    let heuristic = matches.get_one::<String>("heuristic").unwrap().as_str();

    let file_name = format!(
        "src/cputime/{}_{}.txt",
        if use_time_limit { "60sec" } else { "duration" },
        heuristic
    );

    let file = fs::File::create(&file_name).expect("Failed to create file");
    let mut buffered_writer = BufWriter::new(file);

    visit_dirs(Path::new("src/inputs"), &mut buffered_writer, use_time_limit, heuristic)
        .expect("Failed to visit directories");
}

fn visit_dirs(dir: &Path, buffered_writer: &mut BufWriter<fs::File>, use_time_limit: bool, heuristic: &str) -> std::io::Result<()> {
    if dir.is_dir() {
        for entry in fs::read_dir(dir)? {
            let entry = entry?;
            let path = entry.path();
            if path.is_dir() {
                visit_dirs(&path, buffered_writer, use_time_limit, heuristic)?;
            } else if path.extension().unwrap_or_default() == "cnf" {
                run_solver(&path, buffered_writer, use_time_limit, heuristic)?;
            }
        }
    }
    Ok(())
}

fn run_solver(path: &Path, buffered_writer: &mut BufWriter<fs::File>, use_time_limit: bool, heuristic: &str) -> std::io::Result<()> {
    let (sender, receiver) = mpsc::channel();
    let start_time = Instant::now();
    let path_str = path.to_str().unwrap().to_owned();
    let heuristic_clone = heuristic.to_owned();

    thread::spawn(move || {
        let output = Command::new("cargo")
            .args(&["run", "--bin", "dpll", "--", "-m", "dpll", "-i", &path_str, "-H", &heuristic_clone, "-d", "true"])
            .output()
            .expect("Failed to execute command");
        let elapsed_time = start_time.elapsed();
        sender.send((output, elapsed_time)).expect("Failed to send output");
    });

    let result: Result<(Output, Duration), Box<dyn std::error::Error>> = if use_time_limit {
        receiver.recv_timeout(Duration::from_secs(60)).map_err(|e| e.into())
    } else {
        receiver.recv().map_err(|e| e.into())
    };

    match result {
        Ok((output, elapsed_time)) => {
            if !output.status.success() {
                writeln!(buffered_writer, "File: \"{}\", Heuristic: {}, Error: Further warnings or errors occurred. Check logs for details, Execution Time: {}.{}", path.display(), heuristic, elapsed_time.as_secs(), elapsed_time.subsec_micros())?;
                return Ok(());
            }

            let solver_output = str::from_utf8(&output.stdout).unwrap_or("Error while decoding output").trim();
            let result = if solver_output.contains("Unsat") {
                "UNSAT"
            } else if solver_output.contains("Sat") {
                "SAT"
            } else {
                "Unknown Result"
            };

            writeln!(buffered_writer, "File: \"{}\", Heuristic: {}, Result: {}, Execution Time: {}.{}", path.display(), heuristic, result, elapsed_time.as_secs(), elapsed_time.subsec_micros())?;
        },
        Err(_) => {
            writeln!(buffered_writer, "File: \"{}\", Heuristic: {}, Result: Timeout, Execution Time: --", path.display(), heuristic)?;
        }
    }

    buffered_writer.flush()?; 
    Ok(())
}
