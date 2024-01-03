use clap::{command, Arg};
use std::{
    fs::{self, File},
    io::{self, Write, Result},
    path::{Path, PathBuf},
    process::{Command, Stdio},
    str,
    time::{Duration, Instant},
    sync::mpsc,
};
use wait_timeout::ChildExt; 
use threadpool::ThreadPool;

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
    let mut csv_file = File::create(file_name)?;
    writeln!(csv_file, "File,Heuristic,Result,Execution Time")?;

    let cnf_files = find_cnf_files("src/inputs")?;
    let pool = ThreadPool::new(6); 
    let (tx, rx) = mpsc::channel();

    for path in &cnf_files {
        let tx = tx.clone();
        let heuristic_clone = heuristic.to_string();
        let path_clone = path.clone();
        pool.execute(move || {
            let result = if use_time_limit {
                run_solver_with_limit(&path_clone, &heuristic_clone, 60)
            } else {
                run_solver(&path_clone, &heuristic_clone)
            };
            tx.send((path_clone, result)).expect("Failed to send result");
        });
    }

    drop(tx);
    pool.join(); 

    for _ in 0..cnf_files.len() {
        let (path, result) = match rx.recv() {
            Ok(data) => data,
            Err(e) => {
                eprintln!("Failed to receive data: {}", e);
                continue; 
            }
        };
    
        match result {
            Ok((status, duration)) => {
                writeln!(csv_file, "{},{},{},{}", path.display(), heuristic, status, duration)?;
            },
            Err(e) => {
                eprintln!("Error processing file {}: {}", path.display(), e);
            }
        }
    }
    

    csv_file.flush()?; 
    Ok(())
}

fn find_cnf_files<P: AsRef<Path>>(base_path: P) -> io::Result<Vec<PathBuf>> {
    let mut files = Vec::new();
    for entry in fs::read_dir(base_path)? {
        let entry = entry?;
        let path = entry.path();
        if path.is_dir() {
            files.extend(find_cnf_files(path)?);
        } else if path.extension().and_then(|s| s.to_str()) == Some("cnf") {
            files.push(path);
        }
    }
    Ok(files)
}

fn run_solver<P: AsRef<Path>>(path: P, heuristic: &str) -> io::Result<(String, String)> {
    let start = Instant::now();
    let path_str = path.as_ref().to_str().unwrap();

    let output = Command::new("cargo")
        .args(&["run", "--bin", "dpll", "--", "-m", "dpll", "-i", path_str, "-H", heuristic, "-d", "true"])
        .output()?;

    let duration = start.elapsed();
    let solver_output = str::from_utf8(&output.stdout).unwrap_or("Error while decoding output").trim();
    let status = if solver_output.contains("Unsat") {
        "UNSAT"
    } else if solver_output.contains("Sat") {
        "SAT"
    } else {
        "Unknown Result"
    };

    Ok((status.to_string(), format!("{}.{}", duration.as_secs(), duration.subsec_millis())))
}

fn run_solver_with_limit<P: AsRef<Path>>(path: P, heuristic: &str, limit: u64) -> io::Result<(String, String)> {
    let start = Instant::now();
    let path_str = path.as_ref().to_str().unwrap();

    let mut child = Command::new("cargo")
        .args(&["run", "--bin", "dpll", "--", "-m", "dpll", "-i", path_str, "-H", heuristic, "-d", "true"])
        .stdout(Stdio::piped())
        .spawn()?;

    let (status, execution_time) = match child.wait_timeout(Duration::from_secs(limit)).unwrap() {
        Some(status) if status.success() => {
            let output = child.wait_with_output()?;
            let solver_output = str::from_utf8(&output.stdout).unwrap_or("Error while decoding output").trim();
            let result = if solver_output.contains("Unsat") {
                "UNSAT"
            } else if solver_output.contains("Sat") {
                "SAT"
            } else {
                "Unknown Result"
            };
            let duration = start.elapsed();
            (result.to_string(), format!("{}.{}", duration.as_secs(), duration.subsec_millis()))
        },
        Some(_) | None => {
            let _ = child.kill(); 
            ("TIMEOUT".to_string(), "--".to_string())
        }
    };

    Ok((status, execution_time))
}
