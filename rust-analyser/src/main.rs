mod anomalies;
mod classifier;
mod oprecord;

use std::path::PathBuf;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: analyser <trace.jsonl>");
        std::process::exit(1);
    }
    let path = PathBuf::from(&args[1]);
    let history = match oprecord::load_history(&path) {
        Ok(h) => h,
        Err(e) => {
            eprintln!("error reading {}: {}", path.display(), e);
            std::process::exit(2);
        }
    };

    println!("=== Trace summary ===");
    println!("file: {}", path.display());
    println!("operations: {}", history.len());

    let a1 = anomalies::detect_a1(&history);
    let a2 = anomalies::detect_a2(&history);
    let a3 = anomalies::detect_a3(&history);
    let a6 = anomalies::detect_a6(&history);

    println!();
    println!("=== Anomaly detection ===");
    println!("A1 (Stale-Generation):       {} occurrence(s)", a1.len());
    println!("A2 (Phantom-Tool):           {} occurrence(s)", a2.len());
    println!("A3 (Causal-Cascade):         {} occurrence(s)", a3.len());
    println!("A6 (Tool-Effect-Reorder):    {} occurrence(s)", a6.len());

    if !a1.is_empty() {
        println!();
        println!("--- A1 witnesses (first 3) ---");
        for w in a1.iter().take(3) {
            let cell = w.cell.as_deref().unwrap_or("?");
            println!(
                "  i={} j={} cell={}: agent {} read {} at t={}, agent {} wrote {} at t={}, agent {} wrote at t={}",
                w.i,
                w.j,
                cell,
                history[w.i].agent,
                history[w.i].read_values.get(cell).map(|s| s.as_str()).unwrap_or("?"),
                history[w.i].read_time,
                history[w.j].agent,
                history[w.j].write_values.get(cell).map(|s| s.as_str()).unwrap_or("?"),
                history[w.j].write_time,
                history[w.i].agent,
                history[w.i].write_time,
            );
        }
    }

    let level = classifier::classify(&history);
    println!();
    println!("=== Level classification ===");
    println!("Highest level satisfied: {}", level.label());
    println!();
}
