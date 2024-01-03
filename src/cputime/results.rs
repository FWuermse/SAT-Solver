use std::{
    fs::{self, File},
    io::{self, Write, BufReader, BufRead},
    path::Path,
};

fn main() -> io::Result<()> {
    let cputime_path = Path::new("src/cputime");
    let mut results_file = File::create("src/cputime/results.txt")?;

    for entry in fs::read_dir(cputime_path)? {
        let entry = entry?;
        let path = entry.path();
        if let Some(filename) = path.file_name().and_then(|n| n.to_str()) {
            if filename.starts_with("60sec") && filename.ends_with(".csv") {
                let heuristic = filename.strip_prefix("60sec_").unwrap().strip_suffix(".csv").unwrap();
                let file = File::open(&path)?;
                let reader = BufReader::new(file);
                let mut solved = 0;
                let mut incorrectly_solved = Vec::new();
                let mut timeouts = 0;

                for line in reader.lines() {
                    let line = line?;
                    if line.contains("TIMEOUT") {
                        timeouts += 1;
                    } else if let Some(result) = line.split(',').nth(2) {
                        let correct = (line.contains("/sat/") && result == "SAT") ||
                                      (line.contains("/unsat/") && result == "UNSAT");
                        if correct {
                            solved += 1;
                        } else if result == "SAT" || result == "UNSAT" {
                            incorrectly_solved.push(line);
                        }
                    }
                }

                let total_cases = solved + timeouts + incorrectly_solved.len();
                writeln!(results_file, "Heuristic: {}", heuristic)?;
                writeln!(results_file, "Correctly solved: {}", solved)?;
                writeln!(results_file, "Incorrectly solved: {}", incorrectly_solved.len())?;
                writeln!(results_file, "Timeouts: {}", timeouts)?;
                writeln!(results_file, "Total cases: {}", total_cases)?;
                if total_cases != 202 {
                    writeln!(results_file, "WARNING: Total cases do not match expected number (202)")?;
                }
                for line in &incorrectly_solved {
                    writeln!(results_file, "{}", line)?;
                }
                writeln!(results_file, "\n")?;
            }
        }
    }

    Ok(())
}
