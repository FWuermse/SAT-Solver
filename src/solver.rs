use std::{
    fs, io,
    path::{Path, PathBuf},
    time::{Duration, Instant},
};

use crate::{
    cdcl::CDCL,
    cli::Heuristic,
    dpll::DIMACSOutput,
};

fn solve_all_inputs() -> io::Result<()> {
    let files = find_cnf_files("src/inputs")?;
    let mut correct_count = 0;
    let mut false_count = 0;
    let mut time_outs = 0;
    let mut total_time = 0.0;
    let mut errors = 0;

    let total_files = files.len();
    for (index, file) in files.iter().enumerate() {
        println!("Progress: {}/{}", index + 1, total_files);
        let (status, time) = run_solver(&file, Heuristic::Arbitrary, Some(17), true, None)?;
        let expected_status =
            if file.starts_with("src/inputs/sat") || file.starts_with("src/inputs/test/sat") {
                String::from("SAT")
            } else {
                String::from("UNSAT")
            };

        total_time += time.parse::<f64>().unwrap();
        if status == expected_status {
            correct_count += 1;
        } else {
            false_count += 1;
        }

        if status == "Timeout" {
            time_outs += 1;
        }

        if status == "Error" {
            errors += 1;
        }

        println!(
            "File: {:?}, Status: {}, Time: {}, Timeouts: {}, Total Time: {}",
            file,
            status,
            time,
            time_outs,
            format!("{:.1}", total_time)
        );
    }

    println!("Correctly solved: {}", correct_count);
    println!("False solutions: {}", false_count);
    println!("Timeouts: {}", time_outs);
    println!("Errors: {}", errors);
    println!("Total time: {}", format!("{:.1}", total_time));

    Ok(())
}

fn find_cnf_files<P: AsRef<Path>>(dir: P) -> io::Result<Vec<PathBuf>> {
    let mut files = vec![];
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        if path.is_dir() {
            files.append(&mut find_cnf_files(&path)?);
        } else if path.extension().map_or(false, |e| e == "cnf") {
            files.push(path);
        }
    }
    Ok(files)
}
use std::sync::mpsc::channel;
use std::thread;

fn run_solver<P: AsRef<Path>>(
    path: P,
    heuristic: Heuristic,
    restart_threshold: Option<usize>,
    use_luby: bool,
    factor: Option<usize>,
) -> io::Result<(String, String)> {
    let start = Instant::now();
    let (input, v_c, c_c) = crate::parse::parse(path.as_ref().to_str().unwrap()).unwrap();

    let mut solver = CDCL::new(
        input,
        v_c,
        c_c,
        heuristic,
        false,
        restart_threshold,
        use_luby,
        factor,
    );
    let (tx, rx) = channel();

    thread::spawn(move || {
        let result = solver.solve();
        tx.send(result).unwrap();
    });

    let status: String = match rx.recv_timeout(Duration::from_secs(60)) {
        Ok(result) => match result {
            Ok(res) => match res {
                DIMACSOutput::Sat(_) => "SAT".to_string(),
                DIMACSOutput::Unsat => "UNSAT".to_string(),
            },
            Err(_) => "Error".to_string(),
        },
        Err(_) => "Timeout".to_string(),
    };

    let duration = start.elapsed();

    Ok((
        status.to_string(),
        format!("{}.{}", duration.as_secs(), duration.subsec_millis()),
    ))
}

#[test]
fn test_solve_all_inputs() {
    solve_all_inputs().unwrap();
}
