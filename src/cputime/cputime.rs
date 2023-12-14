use std::{fs, process::Command, time::{Duration, Instant}, io::Write, path::Path, thread, sync::mpsc};

/*
Benchmark your solver using the included SATlib benchmarks. 
Given one minute of CPU time for each input, how many problems is your solver able to solve? 
There are some hard problems included, you are not supposed to solve all within that time limit.
*/

fn main() {
    let mut file = fs::File::create("src/cputime/time.txt").expect("Failed to create file");
    visit_dirs(Path::new("dimacs-files/input"), &mut file).expect("Failed to visit directories");
}

fn visit_dirs(dir: &Path, file: &mut fs::File) -> std::io::Result<()> {
    if dir.is_dir() {
        for entry in fs::read_dir(dir)? {
            let entry = entry?;
            let path = entry.path();
            if path.is_dir() {
                visit_dirs(&path, file)?;
            } else if path.extension().unwrap_or_default() == "cnf" {
                run_solver(&path, file)?;
            }
        }
    }
    Ok(())
}

fn run_solver(path: &Path, file: &mut fs::File) -> std::io::Result<()> {
    let (sender, receiver) = mpsc::channel();
    let start_time = Instant::now();
    let path_str = path.to_str().unwrap().to_owned();

    thread::spawn(move || {
        let output = Command::new("cargo")
            .args(&["run", "--bin", "dpll", "--", "-m", "dpll", "-i", &path_str, "-H", "arbitrary", "-d", "true"])
            .output()
            .expect("Failed to execute command");
        let elapsed_time = start_time.elapsed();
        sender.send((output, elapsed_time)).expect("Failed to send output");
    });

    let (output, elapsed_time) = match receiver.recv_timeout(Duration::from_secs(60)) {
        Ok(result) => result,
        Err(_) => {
            writeln!(file, "File: {:?}, Error: Timeout", path)?;
            return Ok(());
        }
    };

    if !output.status.success() {
        writeln!(file, "File: {:?}, Error: Further warnings or errors occurred. Check logs for details.", path)?;
        return Ok(());
    }

    writeln!(file, "File: {:?}, Execution Time: {}.{}", path, elapsed_time.as_secs(), elapsed_time.subsec_micros())?;
    Ok(())
}
