use std::fs;
use std::path::{Path, PathBuf};

use anyhow::{anyhow, Context as _};
use clap::Args;
use clap::{Parser, Subcommand};

use crate::coq::CoqArgs;
use crate::coq::CoqOutputCache;
use crate::debug_print::debug_print_template;
use crate::literate::literate_to_markdown;
use crate::student_repo::create_student_repo;
use crate::template::Template;
use crate::website::create_website;
use crate::{assignment, demo_print};

/// Process literate Coq templates to create Markdown lecture notes.
#[derive(Args)]
struct LiterateArgs {
    /// Path to .v Coq template.
    #[arg(short = 'i', long)]
    pub template: PathBuf,
    /// Translate as solution (default to exercise).
    #[arg(long)]
    pub solution: bool,
    /// Path to .md output markdown file. If a directory, derive the
    /// file name from the input.
    #[arg(short = 'o', long)]
    pub output: PathBuf,
    /// Path to _RocqProject or _CoqProject to get arguments from.
    #[arg(short = 'p', long)]
    pub rocq_project: Option<PathBuf>,
    /// Clear the cache before running.
    #[arg(long)]
    pub no_cache: bool,
    /// Coq arguments for building template.
    pub coq_args: Vec<String>,
}

#[derive(Args)]
struct InputOutput {
    /// Path to output file. If this is a directory, use the filename of the template.
    #[arg(short = 'o', long)]
    pub output: PathBuf,
    /// Path to .v Coq assignment template.
    pub template: PathBuf,
}

#[derive(Subcommand)]
enum Command {
    /// Convert a literate template to a markdown file for the web.
    Literate(LiterateArgs),
    /// Convert a Coq assignment template to an exercise file.
    Exercise(InputOutput),
    /// Convert a Coq assignment template to a solution file.
    Solution(InputOutput),
    /// Convert a Coq assignment to a lecture demo file.
    Demo(InputOutput),
    /// Print a template in debug format.
    ///
    /// Especially useful to inspect how whitespace is parsed.
    Debug {
        /// Path to .v Coq template.
        template: PathBuf,
    },
    /// Create student repo (sys-verif-fa25-proofs).
    Repo {
        /// Output directory. Defaults to ./_built. Safe to run on top of the
        /// student repo, but also won't try to delete anything that shouldn't
        /// be there.
        #[arg(default_value = "./_built")]
        output: PathBuf,
    },
    /// Translate literate files for website repo (sys-verif-fa25).
    Web {
        /// Output directory. Defaults to ./_web.
        #[arg(default_value = "./_web")]
        output: PathBuf,
    },
}

impl InputOutput {
    fn template(&self) -> Result<Template, anyhow::Error> {
        let tmpl = fs::read_to_string(&self.template)
            .with_context(|| format!("could not read template file {}", self.template.display()))?;
        Template::parse(&tmpl).map_err(|err| anyhow!("could not parse template: {err}"))
    }

    fn output_path(&self) -> PathBuf {
        if self.output.is_dir() {
            self.output.join(self.template.file_name().unwrap())
        } else {
            self.output.clone()
        }
    }
}

/// Process templates to create student-facing content.
#[derive(Parser)]
#[command(version, about)]
pub struct App {
    #[command(subcommand)]
    cmd: Command,
}

impl App {
    pub fn exec(&self) -> Result<(), anyhow::Error> {
        match &self.cmd {
            Command::Literate(args) => {
                let mut coq_args = match &args.rocq_project {
                    Some(fname) => CoqArgs::from_rocqproject(fname)?,
                    None => CoqArgs::new(),
                };
                coq_args.extend_args(&args.coq_args);
                let cache = CoqOutputCache::new(coq_args);
                if args.no_cache {
                    cache.clear()?;
                }
                let md = literate_to_markdown(&args.template, args.solution, &cache)?;
                let output = if args.output.is_dir() {
                    let file_name = Path::new(args.template.file_name().unwrap());
                    &args.output.join(file_name.with_extension("md"))
                } else {
                    &args.output
                };

                fs::write(output, md).with_context(|| "could not create output file")?;
            }
            Command::Exercise(args) => {
                let template = args.template()?;
                let output = args.output_path();
                fs::write(&output, assignment::exercise_file(&template)).with_context(|| {
                    format!("could not create output file {}", output.display())
                })?;
            }
            Command::Solution(args) => {
                let template = args.template()?;
                let output = args.output_path();
                fs::write(&output, assignment::solution_file(&template)).with_context(|| {
                    format!("could not create output file {}", output.display())
                })?;
            }
            Command::Demo(args) => {
                let template = args.template()?;
                let output = args.output_path();
                fs::write(&output, demo_print::demo_file(&template)).with_context(|| {
                    format!("could not create output file {}", output.display())
                })?;
            }
            Command::Debug { template } => {
                let tmpl = fs::read_to_string(template).with_context(|| {
                    format!("could not read template file {}", template.display())
                })?;
                let tmpl = Template::parse(&tmpl)
                    .map_err(|err| anyhow!("could not parse template: {err}"))?;
                debug_print_template(&tmpl);
            }
            Command::Repo { output: dst_dir } => create_student_repo(dst_dir)?,
            Command::Web { output: dst_dir } => create_website(dst_dir)?,
        }
        Ok(())
    }

    /// Run template itself, with cmd as the subcommand and args as the remaining
    /// argument.
    pub fn run(cmd: &str, args: &[&str]) -> Result<(), anyhow::Error> {
        let owned_args: Vec<String> = args.iter().map(|s| s.to_string()).collect();
        App::parse_from(
            ["template".to_string(), cmd.to_string()]
                .iter()
                .chain(owned_args.iter()),
        )
        .exec()?;
        Ok(())
    }
}
