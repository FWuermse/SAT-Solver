use clap::{command, Arg};
use csv::Writer;
use std::{
    fs::File,
    io::Result,
    path::Path,
    process::{Command, Output},
    str,
    sync::mpsc,
    thread,
    time::{Duration, Instant},
};

fn main() -> Result<()> {
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
        "src/cputime/{}_{}.csv",
        if use_time_limit { "60sec" } else { "duration" },
        heuristic
    );

    let file = File::create(&file_name)?;
    let mut csv_writer = Writer::from_writer(file);

    csv_writer.write_record(&["File", "Heuristic", "Result", "Execution Time"])?;

    visit_dirs(Path::new("src/inputs"), &mut csv_writer, use_time_limit, heuristic)?;

    Ok(())
}

fn visit_dirs(dir: &Path, csv_writer: &mut Writer<File>, use_time_limit: bool, heuristic: &str) -> Result<()> {
    if dir.is_dir() {
        for entry in std::fs::read_dir(dir)? {
            let entry = entry?;
            let path = entry.path();
            if path.is_dir() {
                visit_dirs(&path, csv_writer, use_time_limit, heuristic)?;
            } else if path.extension().map_or(false, |ext| ext == "cnf") {
                run_solver(&path, csv_writer, use_time_limit, heuristic)?;
            }
        }
    }
    Ok(())
}


fn run_solver(path: &Path, csv_writer: &mut Writer<File>, use_time_limit: bool, heuristic: &str) -> Result<()> {
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

    let result = if use_time_limit {
        match receiver.recv_timeout(Duration::from_secs(60)) {
            Ok(value) => Ok(value),
            Err(e) => Err(std::io::Error::new(std::io::ErrorKind::Other, e))
        }
    } else {
        receiver.recv_timeout(Duration::from_secs(600)).map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, e))
    };

    match result {
        Ok((output, elapsed_time)) => {
            let solver_output = str::from_utf8(&output.stdout).unwrap_or("Error while decoding output").trim();
            let result = if solver_output.contains("Unsat") {
                "UNSAT"
            } else if solver_output.contains("Sat") {
                "SAT"
            } else {
                "Unknown Result"
            };

            csv_writer.write_record(&[
                path.display().to_string(),
                heuristic.to_string(),
                result.to_string(),
                format!("{}.{}", elapsed_time.as_secs(), elapsed_time.subsec_micros())
            ])?;
        },
        Err(_) => {
            csv_writer.write_record(&[
                path.display().to_string(),
                heuristic.to_string(),
                "Timeout".to_string(),
                "--".to_string()
            ])?;
        }
    }

    csv_writer.flush()?; 
    Ok(())
}
