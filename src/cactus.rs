use plotters::prelude::*;
use std::fs::{self, File};
use std::io::{self, BufRead, BufReader, Write};
use std::path::Path;



fn prepare_cactus_data(directory: &str, output_csv: &str) -> io::Result<()> {
    let mut all_runtimes = Vec::new();

    for entry in fs::read_dir(directory)? {
        let entry = entry?;
        let path = entry.path();

        if path.is_file() && path.extension().unwrap_or_default() == "txt" {
            let file = File::open(&path)?;
            let reader = BufReader::new(file);

            for line in reader.lines() {
                let line = line?;
                if let Some(runtime_str) = line.split(',').last() {
                    if let Ok(runtime) = runtime_str.parse::<f64>() {
                        all_runtimes.push(runtime);
                    }
                }
            }
        }
    }

    all_runtimes.sort_by(|a, b| a.partial_cmp(b).unwrap());

    let mut wtr = csv::Writer::from_path(output_csv)?;
    for (idx, runtime) in all_runtimes.iter().enumerate() {
        wtr.write_record(&[idx.to_string(), runtime.to_string()])?;
    }
    wtr.flush()?;

    Ok(())
}

fn read_and_process_data(file_path: &str) -> Vec<f64> {
    let file = File::open(file_path).expect("Failed to open file");
    let reader = BufReader::new(file);

    let mut runtimes: Vec<f64> = reader
        .lines()
        .filter_map(|line| line.ok())
        .filter_map(|line| {
            let parts: Vec<&str> = line.split(',').collect();
            parts.last()?.parse::<f64>().ok()
        })
        .collect();

    runtimes.sort_by(|a, b| a.partial_cmp(b).unwrap());
    runtimes
}


fn create_cactus_plot(data: &[f64], output_path: &str) -> Result<(), Box<dyn std::error::Error>> {
    let root = BitMapBackend::new(output_path, (640, 480)).into_drawing_area();
    root.fill(&WHITE)?;
    let mut chart = ChartBuilder::on(&root)
        .caption("Cactus Plot", ("sans-serif", 50))
        .margin(5)
        .x_label_area_size(30)
        .y_label_area_size(30)
        .build_cartesian_2d(0..data.len(), 0f64..*data.last().unwrap())?;

    chart.configure_mesh().draw()?;

    chart
        .draw_series(LineSeries::new(
            data.iter().enumerate().map(|(x, &y)| (x, y)),
            &RED,
        ))?
        .label("Run Time")
        .legend(|(x, y)| PathElement::new(vec![(x, y), (x + 20, y)], &RED));

    chart.configure_series_labels().draw()?;
    Ok(())
}


fn main() -> io::Result<()> {
    let directory = "src/cputime";
    let output_csv = "output.csv";

    prepare_cactus_data(directory, output_csv)
}
