use std::env;
use std::error::Error;
use std::ffi::OsStr;
use std::path::Path;
use std::process::{Command, ExitCode};
use std::sync::LazyLock;

use clap::{Parser, Subcommand};

static COVERAGE_FOLDER: LazyLock<&Path> = LazyLock::new(|| Path::new("./target/coverage/profraw"));
static PROFILING_FILE_NAME: LazyLock<&Path> = LazyLock::new(|| Path::new("cargo-coverage-%m.profraw"));
static COVERAGE_TARGET_FOLDER: LazyLock<&Path> = LazyLock::new(|| Path::new("./target/coverage/html"));

static CARGO_LOCATION: LazyLock<String> = LazyLock::new(|| env::var("CARGO").unwrap_or("cargo".to_string()));
static GRCOV_LOCATION: LazyLock<&str> = LazyLock::new(|| "grcov");
static XDG_OPEN_LOCATION: LazyLock<&str> = LazyLock::new(|| "xdg-open");

const TEST_FILE_GLOB: &str = "**/*_tests.rs";

/// Line exclusion pattern for `grcov`
///
/// Ignores all attributes, comments, punctuation-full lines, else-clause line, empty lines.
const GRCOV_LINE_EXCL_REGEX: &str = r#"^\s*(#\[.+\]|\/{2}.*|[\(\[]|,?[\)\]][;,]?|\} else \{)?\n?$"#;

#[derive(Parser)]
struct Cli {
    #[command(subcommand)]
    xtask: XTask,
}

#[derive(Subcommand)]
enum XTask {
    /// Generates code coverage artifact
    Coverage {
        /// Open the resulting code coverage report
        #[arg(long)]
        open: bool,
    },
}

fn main() -> ExitCode {
    if let Err(e) = try_main() {
        eprintln!("{e}");
        return ExitCode::FAILURE;
    }

    ExitCode::SUCCESS
}

fn try_main() -> Result<(), Box<dyn Error>> {
    let cli = Cli::parse();
    // let cli = Cli::new("periodical — xtask").arg(Arg::new("open").);

    match cli.xtask {
        XTask::Coverage {
            open,
        } => xtask_coverage(open),
    }
}

fn xtask_coverage(open: bool) -> Result<(), Box<dyn Error>> {
    let mut llvm_profile_file = COVERAGE_FOLDER.to_path_buf();
    llvm_profile_file.push(AsRef::<OsStr>::as_ref(&*PROFILING_FILE_NAME));

    eprintln!("Profiling code…");

    let cargo_test_succeed = Command::new(AsRef::<OsStr>::as_ref(&*CARGO_LOCATION))
        .env("CARGO_INCREMENTAL", "0")
        .env("RUSTFLAGS", "-C instrument-coverage")
        .env("LLVM_PROFILE_FILE", llvm_profile_file)
        .arg("test")
        .arg("--tests") // Only tests, no doc tests
        .arg("--all-features")
        .arg("-q")
        .status()?
        .success();

    if !cargo_test_succeed {
        return Err("Failed to profile code".into());
    }

    eprintln!("Code profiled successfully!");
    eprintln!("Generating code coverage report…");

    let grcov_succeed = Command::new(AsRef::<OsStr>::as_ref(&*GRCOV_LOCATION))
        .arg(".")
        .arg("-b")
        .arg("./target/debug/deps/")
        .arg("-s")
        .arg(".")
        .arg("-t")
        .arg("html")
        .arg("--branch")
        .arg("--llvm")
        .arg("--excl-line")
        .arg(GRCOV_LINE_EXCL_REGEX)
        .arg("--ignore-not-existing")
        .arg("--ignore")
        .arg(TEST_FILE_GLOB)
        .arg("-o")
        .arg(AsRef::<OsStr>::as_ref(&*COVERAGE_TARGET_FOLDER))
        .status()?
        .success();

    if !grcov_succeed {
        return Err("Failed to generate code coverage report".into());
    }

    eprintln!("Generated code coverage report successfully!");

    if open {
        eprintln!("Opening code coverage report…");

        let mut report_index = COVERAGE_TARGET_FOLDER.to_path_buf();
        report_index.push("html/index.html");

        let xdg_open_succeed = Command::new(AsRef::<OsStr>::as_ref(&*XDG_OPEN_LOCATION))
            .arg(report_index)
            .status()?
            .success();

        if !xdg_open_succeed {
            return Err("Failed to open code coverage report".into());
        }

        eprintln!("Opened!");
    }

    Ok(())
}
