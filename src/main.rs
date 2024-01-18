use flame;

pub mod cdcl;
pub mod cli;
pub mod dpll;
mod heuristics;
pub mod parse;

fn main() {
    let arguments = cli::cli();

    if arguments.flamegraph {
        flame::start("main");
    }

    let (vars, v_count, c_count) = parse::parse(&arguments.inputpath).unwrap();
    let depth = arguments.depth;

    if arguments.flamegraph {
        flame::start("main_solve");
    }

    let cert = match arguments.solver.as_str() {
        "dpll" => dpll::DPLL::new(vars, v_count, c_count, arguments.heuristic, depth).solve(),
        "cdcl" => cdcl::CDCL::new(vars, v_count, c_count, depth).solve(),
        otherwise => panic!("{} is not a valid mode.", otherwise),
    };

    if arguments.flamegraph {
        flame::start("main_solve");
    }

    println!("{:?}", cert);

    if arguments.flamegraph {
        flame::end("main");
        //to create flamegraph for profiling. Portrayal does not work properly with usage of multithreading (-> cputime.rs)
        flame::dump_html(std::fs::File::create("src/visuals/graphs/flamegraph.html").unwrap())
            .unwrap();
    }
}
