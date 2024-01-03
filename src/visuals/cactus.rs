use csv::Reader;
use plotters::prelude::*;
use glob::glob;
use std::collections::HashMap;
use std::error::Error;

fn main() -> Result<(), Box<dyn Error>> {
    let patterns = ["src/cputime/60sec_*.csv", "src/cputime/duration_*.csv"];
    let output_dir = "src/visuals/plots";

    std::fs::create_dir_all(output_dir)?;

    for pattern in patterns.iter() {
        let mut all_data: HashMap<String, Vec<f64>> = HashMap::new();

        for entry in glob(pattern)? {
            let path = entry?;
            let heuristic_name = path.file_stem().ok_or("Invalid file name")?.to_str().ok_or("Invalid file name")?;

            let mut rdr = Reader::from_path(&path)?;
            for result in rdr.records() {
                let record = result?;
                let status = &record[2];
                if status == "SAT" || status == "UNSAT" {
                    let execution_time: f64 = record[3].parse().unwrap_or(0.0);
                    all_data.entry(heuristic_name.to_string()).or_insert_with(Vec::new).push(execution_time);
                }
            }
        }

        if !all_data.is_empty() {
            let plot_name = if pattern.contains("60sec") { "60sec" } else { "duration" };
            create_cactus_plot(&all_data, plot_name, output_dir)?;
        }
    }

    Ok(())
}

fn create_cactus_plot(data: &HashMap<String, Vec<f64>>, plot_name: &str, output_dir: &str) -> Result<(), Box<dyn Error>> {
    let output_file = format!("{}/{}_cactus_plot.png", output_dir, plot_name);
    let root = BitMapBackend::new(&output_file, (640, 480)).into_drawing_area();
    root.fill(&WHITE)?;

    let margin = 20;
    let mut chart = ChartBuilder::on(&root)
        .caption(format!("Cactus Plot: {}", plot_name), ("sans-serif", 40).into_font())
        .margin(margin)
        .x_label_area_size(35)
        .y_label_area_size(40)
        .build_cartesian_2d(0..data.values().map(|v| v.len()).max().unwrap_or(0), 0f64..60f64)?;

    chart.configure_mesh()
        .x_desc("Number of Solved Instances")
        .y_desc("Execution Time (s)")
        .draw()?;

    let mut color_index = 0;
    for (heuristic, times) in data {
        let mut sorted_times = times.clone();
        sorted_times.sort_by(|a, b| a.partial_cmp(b).unwrap());

        let points: Vec<(usize, f64)> = sorted_times.iter().enumerate().map(|(idx, &time)| (idx + 1, time)).collect();
        
        let color = Palette99::pick(color_index);
        chart.draw_series(
            LineSeries::new(points, &color)
        )?.label(heuristic)
         .legend(move |(x, y)| PathElement::new(vec![(x, y), (x + 20, y)], &color));
    
        color_index += 1;
    }

    chart.configure_series_labels()
        .border_style(&BLACK)
        .position(SeriesLabelPosition::UpperLeft)
        .draw()?;

    Ok(())
}
