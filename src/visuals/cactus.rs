use plotters::prelude::*;
use csv::Reader;
use std::error::Error;
use glob::glob;
use std::collections::HashMap;

fn main() -> Result<(), Box<dyn Error>> {
    // Define file patterns and output directory
    let patterns = ["src/cputime/60sec_*.csv", "src/cputime/duration_*.csv"];
    let output_dir = "src/visuals/plots";

    // Create the output directory if it doesn't exist
    std::fs::create_dir_all(output_dir)?;

    // Iterate over each pattern
    for pattern in patterns.iter() {
        // Create a HashMap to store the data
        let mut all_data: HashMap<String, Vec<f64>> = HashMap::new();

        // Iterate over each file matching the pattern
        for entry in glob(pattern)? {
            let path = entry?;
            let file_name = path.file_stem().ok_or("Invalid file name")?.to_str().ok_or("Invalid file name")?;

            // Read the CSV file
            let path_clone = path.clone();
            let mut rdr = Reader::from_path(path_clone)?;
        
            // Iterate over each record in the CSV file
            for result in rdr.records() {
                let record = result?;
                let execution_time: f64 = record[3].parse().unwrap_or(0.0);
                // Insert the execution time into the HashMap
                all_data.entry(file_name.to_string()).or_insert_with(Vec::new).push(execution_time);
            }
        }

        // If the HashMap is not empty, create a cactus plot
        if !all_data.is_empty() {
            if pattern.contains("60sec")
            {
                create_cactus_plot(&all_data, "60sec", output_dir)?;
            }
            else if pattern.contains("duration")
            {
                create_cactus_plot(&all_data, "duration", output_dir)?;
            }

        }
    }

    Ok(())
}

// Function to create a cactus plot
fn create_cactus_plot(data: &HashMap<String, Vec<f64>>, plot_name: &str, output_dir: &str) -> Result<(), Box<dyn Error>> {
    // Define the output file path
    let output_file = format!("{}/{}_cactus_plot.png", output_dir, plot_name);
    // Create a drawing area
    let root = BitMapBackend::new(&output_file, (640, 480)).into_drawing_area();
    root.fill(&WHITE)?;

    let margin = 20; // Margin size in pixels

    // Create a chart with labels and margins
    let mut chart = ChartBuilder::on(&root)
        .caption(format!("Cactus Plot: {}", plot_name), ("sans-serif", 40).into_font())
        .margin(margin)
        .x_label_area_size(35)
        .y_label_area_size(40)
        .build_cartesian_2d(0..data.values().map(|v| v.len()).max().unwrap_or(0), 0f64..60f64)?;

    // Configure the mesh of the chart
    chart.configure_mesh()
        .x_desc("Number of Solved Instances")
        .y_desc("Execution Time (s)")
        .draw()?;

    let mut color_index = 0;
    // Iterate over each heuristic and its corresponding execution times
    for (heuristic, times) in data {
        let mut sorted_times = times.clone();
        sorted_times.sort_by(|a, b| a.partial_cmp(b).unwrap());
    
        // Calculate the cumulative sum of the execution times
        let mut cumulative_sum = 0.0; 
        let points: Vec<(usize, f64)> = sorted_times.iter().enumerate().map(|(idx, &time)| {
            cumulative_sum += time;
            (idx + 1, cumulative_sum)
        }).collect();
        
        let color = Palette99::pick(color_index);
        let legend_color_index = color_index; 
    
        // Draw a line series for each heuristic
        chart.draw_series(
            LineSeries::new(points, &color)
        )?.label(heuristic)
         .legend(move |(x, y)| {
            let legend_color = Palette99::pick(legend_color_index);
            PathElement::new(vec![(x, y), (x + 20, y)], &legend_color)
        });
    
        color_index += 1;
    }
    
    // Configure the series labels of the chart
    chart.configure_series_labels()
        .border_style(&BLACK)
        .position(SeriesLabelPosition::UpperLeft)
        .draw()?;

    Ok(())
}
