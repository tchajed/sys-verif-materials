//! Process literate files for the website.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{anyhow, Context as _};
use rayon::prelude::*;

use crate::app::App;

#[derive(Debug, Clone)]
struct LiterateCmd {
    src_path: PathBuf,
    output_path: PathBuf,
    is_solution: bool,
}

impl LiterateCmd {
    fn new_soln_or_exercise(
        src_path: PathBuf,
        output_path: impl AsRef<Path>,
        is_solution: bool,
    ) -> Self {
        Self {
            src_path,
            output_path: output_path.as_ref().to_path_buf(),
            is_solution,
        }
    }

    fn new(src_path: PathBuf, output_path: impl AsRef<Path>) -> Self {
        Self::new_soln_or_exercise(src_path, output_path, false)
    }

    #[allow(dead_code)]
    fn new_solution(src_path: PathBuf, output_path: impl AsRef<Path>) -> Self {
        Self::new_soln_or_exercise(src_path, output_path, true)
    }

    fn run(&self, web: &Path) -> anyhow::Result<()> {
        let output_path = web.join(&self.output_path);
        let src_str = self.src_path.to_string_lossy();
        let output_str = output_path.to_string_lossy();

        let mut args = vec!["--rocq-project", "_RocqProject"];

        if self.is_solution {
            args.push("--solution");
        }

        args.extend(["--template", &src_str, "--output", &output_str]);

        App::run("literate", &args)
    }
}

fn process_notes() -> anyhow::Result<Vec<LiterateCmd>> {
    let notes_dir = Path::new("src/sys_verif/notes");
    let mut commands = Vec::new();

    for entry in fs::read_dir(notes_dir)? {
        let entry = entry?;
        let path = entry.path();
        if path.extension().is_some_and(|ext| ext == "v") {
            // TODO: gradually release solutions versions of notes
            commands.push(LiterateCmd::new(path, "docs/notes/"));
        }
    }

    Ok(commands)
}

fn process_assignments(web: &Path) -> anyhow::Result<Vec<LiterateCmd>> {
    let assignments = ["hw1", "hw3", "hw4"];
    let mut commands = Vec::new();

    for assignment in &assignments {
        let assignment_dir = PathBuf::from("src/sys_verif/assignment_solns").join(assignment);

        // Create output directory
        let output_dir = web.join("docs/assignments").join(assignment);
        fs::create_dir_all(&output_dir)?;

        for entry in fs::read_dir(&assignment_dir)? {
            let entry = entry?;
            let path = entry.path();
            if path.extension().is_some_and(|ext| ext == "v") {
                let relative_out = format!("docs/assignments/{}/", assignment);
                commands.push(LiterateCmd::new(path, relative_out));
            }
        }
    }

    Ok(commands)
}

fn process_program_proofs_guide() -> anyhow::Result<Vec<LiterateCmd>> {
    let guide_dir = Path::new("src/sys_verif/program_proof/guide");
    let mut commands = Vec::new();

    for entry in fs::read_dir(guide_dir)? {
        let entry = entry?;
        let path = entry.path();
        if path.extension().is_some_and(|ext| ext == "v") {
            commands.push(LiterateCmd::new(path, "docs/notes/program-proofs/"));
        }
    }

    Ok(commands)
}

fn process_program_proofs_demos() -> anyhow::Result<Vec<LiterateCmd>> {
    let demos_dir = Path::new("src/sys_verif/program_proof/demos");
    let mut commands = Vec::new();

    for entry in fs::read_dir(demos_dir)? {
        let entry = entry?;
        let path = entry.path();
        if path.extension().is_some_and(|ext| ext == "v") {
            commands.push(LiterateCmd::new(path, "docs/notes/program-proofs/demos/"));
        }
    }

    Ok(commands)
}

fn run_prettier(web: &Path) -> anyhow::Result<()> {
    // Get list of changed files
    let git_output = Command::new("git")
        .args(["diff", "--name-only", "--diff-filter=ACMR"])
        .current_dir(web)
        .output()
        .context("Failed to get git diff")?;

    if !git_output.status.success() {
        return Err(anyhow!(
            "git diff failed: {}",
            String::from_utf8_lossy(&git_output.stderr)
        ));
    }

    let files = String::from_utf8_lossy(&git_output.stdout);
    let files = files.trim();

    if !files.is_empty() {
        let file_list: Vec<&str> = files.lines().collect();

        let mut cmd = Command::new("pnpm");
        cmd.args([
            "prettier",
            "--log-level",
            "error",
            "--ignore-unknown",
            "--write",
        ]);
        cmd.args(&file_list);
        cmd.current_dir(web);

        let output = cmd.output().context("Failed to run prettier")?;

        if !output.status.success() {
            return Err(anyhow!(
                "prettier failed: {}",
                String::from_utf8_lossy(&output.stderr)
            ));
        }
    }

    Ok(())
}

pub fn create_website(web: &Path) -> anyhow::Result<()> {
    if !web.exists() || !web.is_dir() {
        // no attempt to create output directories - website needs the rest of
        // the setup anyway
        return Err(anyhow!(
            "web repo path does not exist or is not a directory"
        ));
    }
    // resolve web before changing directory
    let web = &web
        .canonicalize()
        .context("Failed to canonicalize web path")?;

    // Change working directory to the sys-verif-solutions repo (parent of template)
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    std::env::set_current_dir(Path::new(manifest_dir).parent().unwrap())
        .context("Failed to set working directory")?;

    // Collect all literate commands
    let mut all_commands = Vec::new();

    // Process lecture notes and run prettier. This puts these changes on disk
    // first, for fast previewing.
    all_commands.extend(process_notes()?);

    // Process assignments (needs web path for directory creation)
    all_commands.extend(process_assignments(web)?);

    // Process program proof guide
    all_commands.extend(process_program_proofs_guide()?);

    // Process program proof demos
    all_commands.extend(process_program_proofs_demos()?);

    // Run everything, then re-format with prettier.
    all_commands.par_iter().try_for_each(|cmd| cmd.run(web))?;
    run_prettier(web)?;

    Ok(())
}
