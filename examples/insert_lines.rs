use clap::Parser;
use patricia_tree::PatriciaSet;
use std::collections::{BTreeSet, HashSet};
use std::io::BufRead;

#[derive(Parser)]
struct Args {
    #[clap(
        long,
        default_value = "patricia",
        value_parser = clap::builder::PossibleValuesParser::new(["patricia", "hash", "btree", "count"])
    )]
    kind: String,
}

fn main() {
    let args = Args::parse();

    match args.kind.as_str() {
        "patricia" => {
            let mut set = PatriciaSet::new();
            each_line(|line| {
                set.insert(line);
            });
            println!("# LINES: {}", set.len());
        }
        "hash" => {
            let mut set = HashSet::new();
            each_line(|line| {
                set.insert(line);
            });
            println!("# LINES: {}", set.len());
        }
        "btree" => {
            let mut set = BTreeSet::new();
            each_line(|line| {
                set.insert(line);
            });
            println!("# LINES: {}", set.len());
        }
        "count" => {
            let mut count = 0;
            each_line(|_| {
                count += 1;
            });
            println!("# LINES: {}", count);
        }
        _ => unreachable!(),
    }
}

fn each_line<F>(mut f: F)
where
    F: FnMut(String),
{
    let stdin = std::io::stdin();
    for line in stdin.lock().lines() {
        f(line.unwrap());
    }
}
