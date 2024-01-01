use plotters::prelude::*;
use csv::Reader;
use std::error::Error;
use glob::glob;


fn main() -> Result<(), Box<dyn Error>> {
    let pattern = "src/cputime/*.csv";
    let output_dir = "src/visuals/plots";

    std::fs::create_dir_all(output_dir)?;

    for entry in glob(pattern)? {
        let path = entry?;
        let file_name = path.file_stem().ok_or("Invalid file name")?.to_str().ok_or("Invalid file name")?;
        
        create_plot(path.to_str().ok_or("Invalid path")?, file_name, output_dir)?;
    }

    Ok(())
}

fn create_plot(file_path: &str, file_name: &str, output_dir: &str) -> Result<(), Box<dyn Error>> {
    let mut rdr = Reader::from_path(file_path)?;
    let mut data: Vec<(String, f64)> = Vec::new();

    for result in rdr.records() {
        let record = result?;
        let instance_name = &record[0];
        let execution_time: f64 = record[3].parse().unwrap_or(0.0);

        data.push((instance_name.to_string(), execution_time));
    }


    let output_file = format!("{}/{}_plot.png", output_dir, file_name);
    let root = BitMapBackend::new(&output_file, (640, 480)).into_drawing_area();
    root.fill(&WHITE)?;

    let mut chart = ChartBuilder::on(&root)
        .caption(format!("Execution Time Plot: {}", file_name), ("sans-serif", 40).into_font())
        .x_label_area_size(35)
        .y_label_area_size(40)
        .build_cartesian_2d(0..data.len(), 0f64..60f64)?;

    chart.configure_mesh().draw()?;

    chart.draw_series(
        data.iter().enumerate().map(|(idx, &(_, y))| {
            Circle::new((idx, y), 3, &RED)
        }),
    )?;

    Ok(())
}
