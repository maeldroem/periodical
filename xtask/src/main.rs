use std::error::Error;
use std::ffi::OsStr;
use std::fmt::Display;
use std::io;
use std::path::Path;
use std::process::{Command, ExitCode};
use std::sync::LazyLock;

use clap::{Parser, Subcommand};

const RUSTUP_BIN_LOCATION: &str = "rustup";
const GRCOV_BIN_LOCATION: &str = "grcov";
const OPEN_BIN_LOCATION: &str = "xdg-open";

static PROFILING_DATA_FOLDER: LazyLock<&Path> = LazyLock::new(|| Path::new("target/profiling"));
static CODE_COVERAGE_REPORT_TARGET: LazyLock<&Path> = LazyLock::new(|| Path::new("target/coverage"));

const PROFILING_DATA_NAME_TEMPLATE: &str = "cargo_coverage_%p_%m.profraw";

const TEST_FILE_GLOB: &str = "src/**/*_tests.rs";

/// Line exclusion pattern for `grcov`
///
/// Ignores all attributes, comments, punctuation-full lines, else-clause line,
/// lines with `unreachable!` invocations, and empty lines.
const GRCOV_LINE_EXCL_REGEX: &str =
    r"^\s*(#\[.+\]|\/{2}.*|[\(\[\{]+|,?[\)\]\}]+[;,]?|\} else \{|.+?unreachable!.+)?\n?$";

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum RustToolchain {
    Stable,
    Nightly,
}

impl Display for RustToolchain {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Stable => write!(f, "stable"),
            Self::Nightly => write!(f, "nightly"),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Hash)]
struct GetRustBinError;

impl Display for GetRustBinError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "An error occurred when trying to retrieve a Rust binary")
    }
}

fn get_rust_bin(bin: &str, toolchain: RustToolchain) -> Result<String, GetRustBinError> {
    let rustup_which_output = Command::new(RUSTUP_BIN_LOCATION)
        .arg("which")
        .arg("--toolchain")
        .arg(toolchain.to_string())
        .arg(bin)
        .output()
        .or(Err(GetRustBinError))?;

    Ok(String::from_utf8(rustup_which_output.stdout)
        .or(Err(GetRustBinError))?
        .trim()
        .to_string())
}

#[derive(Debug)]
enum XtaskError {
    IoError(io::Error),
    TaskError(String),
}

impl Display for XtaskError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::IoError(err) => err.fmt(f),
            Self::TaskError(err) => err.fmt(f),
        }
    }
}

impl Error for XtaskError {}

impl From<io::Error> for XtaskError {
    fn from(value: io::Error) -> Self {
        Self::IoError(value)
    }
}

impl From<GetRustBinError> for XtaskError {
    fn from(value: GetRustBinError) -> Self {
        Self::TaskError(value.to_string())
    }
}

impl From<&str> for XtaskError {
    fn from(value: &str) -> Self {
        Self::TaskError(value.to_string())
    }
}

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
    /// Checks source code formatting
    FmtCheck,
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

    match cli.xtask {
        XTask::Coverage {
            open,
        } => xtask_coverage(open).map_err(Box::<dyn Error>::from),
        XTask::FmtCheck => xtask_fmtcheck().map_err(Box::<dyn Error>::from),
    }
}

fn xtask_coverage(open: bool) -> Result<(), XtaskError> {
    let mut llvm_profile_file = PROFILING_DATA_FOLDER.to_path_buf();
    llvm_profile_file.push(PROFILING_DATA_NAME_TEMPLATE);

    eprintln!("Retrieving stable cargo…");

    let stable_cargo = get_rust_bin("cargo", RustToolchain::Stable)?;

    eprintln!("Done.");

    eprintln!("Profiling code…");

    let cargo_test_succeed = Command::new(stable_cargo)
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

    let grcov_succeed = Command::new(GRCOV_BIN_LOCATION)
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
        .arg(AsRef::<OsStr>::as_ref(*CODE_COVERAGE_REPORT_TARGET))
        .status()?
        .success();

    if !grcov_succeed {
        return Err("Failed to generate code coverage report".into());
    }

    eprintln!("Generated code coverage report successfully!");

    if open {
        eprintln!("Opening code coverage report…");

        let mut report_index = CODE_COVERAGE_REPORT_TARGET.to_path_buf();
        report_index.push("html/index.html");

        let open_succeed = Command::new(OPEN_BIN_LOCATION).arg(report_index).status()?.success();

        if !open_succeed {
            return Err("Failed to open code coverage report".into());
        }

        eprintln!("Opened!");
    }

    Ok(())
}

fn xtask_fmtcheck() -> Result<(), XtaskError> {
    eprintln!("Retrieving stable cargo");

    let stable_cargo = get_rust_bin("cargo", RustToolchain::Stable)?;

    eprintln!("Done.");
    eprintln!("Running clippy…");

    let clippy_succeed = Command::new(&stable_cargo)
        .arg("clippy")
        .arg("-q")
        .arg("--all-targets")
        .status()?
        .success();

    if !clippy_succeed {
        return Err("Some clippy lints were not respected!".into());
    }

    eprintln!("No broken clippy lints detected.");
    eprintln!("Retrieving nightly rustfmt");

    let nightly_rustfmt = get_rust_bin("rustfmt", RustToolchain::Nightly)?;

    eprintln!("Done.");
    eprintln!("Checking source code formatting…");

    let cargo_fmt_succeed = Command::new(&stable_cargo)
        .env("RUSTFMT", &nightly_rustfmt)
        .arg("fmt")
        .arg("-q")
        .arg("--check")
        .arg("--")
        .arg("--unstable-features")
        .status()?
        .success();

    if !cargo_fmt_succeed {
        return Err("Some source code files were not formatted correctly!".into());
    }

    eprintln!("Source code is well-formatted.");

    Ok(())
}
