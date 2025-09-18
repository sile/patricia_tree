use patricia_tree::PatriciaSet;
use std::collections::{BTreeSet, HashSet};
use std::io::BufRead;

fn main() -> noargs::Result<()> {
    let mut args = noargs::raw_args();
    noargs::HELP_FLAG.take_help(&mut args);

    let kind = noargs::opt("kind")
        .doc("Data structure kindt")
        .ty("patricia | hash | btree | count")
        .default("patricia")
        .take(&mut args)
        .then(|a| {
            let value = a.value();
            match value {
                "patricia" | "hash" | "btree" | "count" => Ok(value.to_string()),
                _ => Err("must be one of: patricia, hash, btree, count"),
            }
        })?;
    if let Some(help) = args.finish()? {
        print!("{help}");
        return Ok(());
    }

    match kind.as_str() {
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

    Ok(())
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
